"""Saved, kernel-replayed runtime instruction samples (not a universal CPython proof)."""
from __future__ import annotations

from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import subprocess

from .native_runtime import Object, Global, Bound, Deferred, Iterator, InterfaceError, UNBOUND, Finished, Failed
from .verified_native import quote, lean_value, lean_program
from .verified_backend import lean_list, project_root, audit_axioms, provenance


class Registry:
    def __init__(self): self.objects, self.ids = [], {}

    def value(self, value):
        if value is UNBOUND: return ".unbound"
        if type(value) in (type(None), bool, int, str): return "(" + lean_value(value) + ")"
        if isinstance(value, Global): return "(.global " + quote(value.name) + ")"
        if isinstance(value, Bound): return "(.bound " + self.value(value.value) + " " + quote(value.name) + ")"
        if isinstance(value, Deferred):
            return "(.deferred " + self.value(value.target) + " " + self.values(value.args) + " " + self.keywords(value.keywords) + ")"
        if isinstance(value, Exception):
            name = value.name if isinstance(value, InterfaceError) else type(value).__name__
            return "(.exception " + quote(name) + " " + self.values(value.args) + ")"
        if type(value) not in (Object, dict, Counter, list, tuple, set, range, Iterator): raise TypeError(type(value))
        if id(value) not in self.ids:
            self.ids[id(value)] = len(self.objects)
            self.objects.append(value)
            self.object(value)  # register children in allocation/discovery order
        return f"(.ref {self.ids[id(value)]})"

    def values(self, values): return lean_list(self.value(v) for v in values)
    def keywords(self, fields): return lean_list("(" + quote(k) + ", " + self.value(v) + ")" for k,v in fields.items())
    def pairs(self, pairs): return lean_list("(" + self.value(k) + ", " + self.value(v) + ")" for k,v in pairs)

    def object(self, obj):
        if isinstance(obj, Object):
            return "{kind := " + quote(obj.kind) + ", entries := " + self.pairs(obj.fields.items()) + "}"
        if isinstance(obj, dict):
            return "{kind := " + quote(type(obj).__name__) + ", entries := " + self.pairs(obj.items()) + "}"
        if isinstance(obj, set):
            return "{kind := \"set\", entries := " + self.pairs((v,None) for v in obj) + "}"
        if isinstance(obj, Iterator):
            return "{kind := \"iterator\", source := " + self.value(obj.values) + f", cursor := {obj.index}, expected := {obj.size}" + "}"
        return "{kind := " + quote(type(obj).__name__) + ", items := " + self.values(obj) + "}"

    def error(self, error):
        name = error.name if isinstance(error, InterfaceError) else type(error).__name__
        args = error.args if isinstance(error, (InterfaceError, KeyError, AttributeError)) else ()
        return "(" + quote(name) + ", " + self.values(args) + ")"

    def snapshot(self, task):
        frames = []
        for frame in reversed(task.frames):
            # Inputs must be discovered before temporary stack values.
            arguments = self.values(frame.arguments)
            locals_ = self.values(frame.locals)
            stack = self.values(reversed(frame.stack))
            constructor = "none" if frame.constructor is None else "some " + self.value(frame.constructor)
            frames.append("⟨" + ", ".join((quote(frame.name), str(frame.pc), locals_, arguments, stack, str(frame.attempt), constructor)) + "⟩")
        if task.pending:
            pending = task.pending
            phase = ".waiting ⟨" + ", ".join((quote(pending.interface), self.value(pending.receiver),
                self.values(pending.args), self.keywords(pending.keywords))) + "⟩"
        elif isinstance(task.result, Finished): phase = ".done " + self.value(task.result.value)
        elif isinstance(task.result, Failed): phase = ".failed " + self.error(task.result.error)
        else: phase = ".running"
        # Rendering the registry also discovers objects newly installed in fields.
        heap, index = [], 0
        while index < len(self.objects):
            heap.append(self.object(self.objects[index])); index += 1
        output = lean_list(quote(event[1]) for event in task.events if event[0] == "print")
        return "⟨" + ", ".join((lean_list(heap), lean_list(frames), "0", str(task.sequence), phase, output)) + "⟩"


class Recorder:
    def __init__(self, per_signature=2):
        self.samples, self.counts, self.registries = [], Counter(), []
        self.per_signature = per_signature

    def attach(self, task):
        registry = Registry()
        self.registries.append(registry)
        original = task.step
        def step():
            if task.pending is not None or task.result is not None: return original()
            frame = task.frames[-1]
            instruction = list(task.fetch(frame.pc))
            signature = tuple(instruction)
            before = registry.snapshot(task)
            original()
            after = registry.snapshot(task)
            # Select by opcode and operand (e.g. each method/operator), not by PC.
            signature = (*signature, "error" if isinstance(task.result, Failed) else "normal")
            if self.counts[signature] < self.per_signature:
                self.samples.append(dict(instruction=instruction, before=before, after=after))
                self.counts[signature] += 1
        task.step = step
        original_receive = task.receive
        def receive(token, value=None, error=None):
            # The environment supplies reply objects in the shared heap. Register
            # them before the suspension snapshot; resume itself does not allocate.
            response = ".ok " + registry.value(value) if error is None else ".error " + registry.error(error)
            before = registry.snapshot(task)
            original_receive(token, value, error)
            after = registry.snapshot(task)
            signature = ("reply", token.interface, "ok" if error is None else error.name)
            if self.counts[signature] < self.per_signature:
                self.samples.append(dict(reply=response, epoch=token.sequence, before=before, after=after))
                self.counts[signature] += 1
        task.receive = receive
        return task

    def check(self, bundle, directory, *, standalone=False):
        directory = Path(directory).resolve()
        directory.mkdir(parents=True, exist_ok=True)
        status = directory / "runtime-status.json"
        status.write_text(json.dumps({"sampled_runtime": "not-established"}) + "\n")
        tooling = provenance()
        if tooling != bundle.artifact["toolchain_sources"]: raise ValueError("tooling changed; recompile")
        if hashlib.sha256(Path(bundle.artifact["source_path"]).read_bytes()).hexdigest() != bundle.artifact["source_sha256"]:
            raise ValueError("source changed; recompile")
        if not standalone:
            evidence = json.loads((directory / "status.json").read_text())
            if evidence["translation"] != "checked": raise ValueError("certify translation before replaying runtime samples")
            for file, key in (("bundle.json","bundle_sha256"),("Certificate.lean","certificate_sha256"),("Certificate.olean","checked_module_sha256")):
                if hashlib.sha256((directory / file).read_bytes()).hexdigest() != evidence[key]:
                    raise ValueError("stale or tampered compiler evidence: " + file)
            if json.dumps(bundle.artifact, indent=2)+"\n" != (directory / "bundle.json").read_text():
                raise ValueError("runtime bundle differs from checked source")
        imports = ["import ReactiveModules", "open ReactiveModules Objects"] if standalone else ["import Certificate", "open ReactiveModules Objects Verified"]
        text = [*imports, "namespace NativeRuntimeChecks",
                "set_option maxRecDepth 100000", "set_option maxHeartbeats 100000000"]
        if standalone: text.append("def native_program : Native.Program := " + lean_program(bundle.artifact["native_program"]))
        for index, sample in enumerate(self.samples):
            if "reply" in sample:
                proposition = f"Native.agrees (Native.resume native_program before_{index} 0 {sample['epoch']} ({sample['reply']})) after_{index}"
            else:
                op,a,b = sample["instruction"]
                proposition = f"(Native.select ((before_{index}.frames.head?).map Native.Frame.pc |>.getD 0) 0 native_program.code == ⟨{op},{a},{b}⟩) && Native.agrees (Native.execute native_program before_{index} ⟨{op},{a},{b}⟩) after_{index}"
            text += [f"def before_{index} : Native.State := {sample['before']}",
                     f"def after_{index} : Native.State := {sample['after']}",
                     f"theorem sample_{index} : ({proposition}) = true := by decide +kernel",
                     f"#print axioms sample_{index}"]
        text.append("end NativeRuntimeChecks\n")
        proof = directory / "RuntimeChecks.lean"
        proof.write_text("\n".join(text))
        (directory / "runtime-samples.json").write_text(json.dumps(self.samples, indent=2) + "\n")
        env = dict(os.environ, LEAN_PATH=str(directory) + os.pathsep + os.environ.get("LEAN_PATH", ""))
        result = subprocess.run(["lake", "env", "lean", str(proof)], cwd=project_root(), env=env,
                                text=True, capture_output=True)
        log = result.stdout + result.stderr
        (directory / "runtime-audit.log").write_text(log)
        if result.returncode: raise ValueError("runtime/model sample failed; see " + str(directory / "runtime-audit.log") + "\n" + log[-6000:])
        audit_axioms(log)
        if tooling != provenance() or hashlib.sha256(Path(bundle.artifact["source_path"]).read_bytes()).hexdigest() != bundle.artifact["source_sha256"]:
            raise ValueError("source or tooling changed during replay; rerun")
        status.write_text(json.dumps(dict(sampled_runtime="checked", samples=len(self.samples),
            compiler_connection="not-checked-standalone" if standalone else "checked",
            source_sha256=bundle.artifact["source_sha256"], proof_sha256=hashlib.sha256(proof.read_bytes()).hexdigest(),
            scope="sampled runtime/model agreement, not a universal CPython equivalence proof"), indent=2)+"\n")
