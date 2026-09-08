"""Native object/async source -> RM instruction selection + Lean object machine.

Python AST elaboration and external adapters remain explicit trust boundaries.
The artifact includes every instruction, literal, call frame, retry policy and
interface; none of these are supplied by a per-algorithm source generator.
"""
from __future__ import annotations

import hashlib
import dataclasses
import json
from pathlib import Path
import sys

from .native_frontend import Frontend
from .native_runtime import Machine, Object, Finished
from .verified import INT, Type
from .verified_backend import VerificationBundle, make_bundle, evaluate, lean_list


PAGE = 32  # certificate partition size, never a state/execution bound


def instruction_source(code, base=0):
    source = ["ret", [["lit", 15], ["lit", 0], ["lit", 0]]]
    for pc in reversed(range(len(code))):
        source = ["branch", ["bin", "eq", ["var", 0], ["lit", pc+base]],
                  ["ret", [["lit", n] for n in code[pc]]], source]
    return source


def quote(text):
    # Lean string syntax is JSON-compatible for the supported escaped characters.
    return json.dumps(text, ensure_ascii=False)


def lean_value(value):
    if value is None: return ".nil"
    if type(value) is bool: return ".bool " + str(value).lower()
    if type(value) is int: return f".int ({value})"
    if type(value) is str: return ".str " + quote(value)
    raise TypeError("literal outside native schema")


def lean_program(program, code=None):
    code = code or lean_list(f"⟨{op}, {a}, {b}⟩" for op, a, b in program["instructions"])
    pool = lean_list(".names " + lean_list(map(quote, value)) if tag == "data" else
                     ".value (" + lean_value(value) + ")" for tag, value in program["pool"])
    functions = []
    for name, fn in program["functions"].items():
        retry = fn["retry"] or {}
        functions.append("⟨" + ", ".join((quote(name), str(fn["entry"]), lean_list(map(quote, fn["parameters"])),
            str(len(fn["locals"])), str(fn["asynchronous"]).lower(), quote(retry.get("exception", "")), str(retry.get("tries", 1)))) + "⟩")
    classes = lean_list("(" + quote(name) + ", " + lean_list("(" + quote(method) + ", " + quote(target) + ")"
        for method, target in methods.items()) + ")" for name, methods in program["classes"].items())
    interfaces = []
    for name, declaration in program["interfaces"].items():
        kind = declaration if isinstance(declaration, str) else "external"
        methods = declaration.get("async_methods", []) if isinstance(declaration, dict) else []
        interfaces.append("⟨" + quote(name) + ", " + quote(kind) + ", " + lean_list(map(quote, methods)) + "⟩")
    return "⟨" + ", ".join((code, pool, lean_list(functions), classes, lean_list(interfaces))) + "⟩"


class NativeBundle(VerificationBundle):
    def validate_source(self):
        path = Path(self.artifact["source_path"])
        fresh = Frontend(path.read_text(), path, self.artifact["model_config"].get("interfaces", {})).artifact()
        if fresh != self.artifact["native_program"]: raise ValueError("native source/control/schema differs; recompile")
        expected = {f"native_page_{base//PAGE}" for base in range(0, len(fresh["instructions"]), PAGE)}
        if set(self.artifact["functions"]) != expected: raise ValueError("instruction pages differ from source")
        for base in range(0, len(fresh["instructions"]), PAGE):
            fn = self.artifact["functions"][f"native_page_{base//PAGE}"]
            if fn["source"] != instruction_source(fresh["instructions"][base:base+PAGE], base):
                raise ValueError("instruction dispatch differs from source")
            if fn["slots"] != ["int"] or fn["inputs"] != 1 or fn["output_sorts"] != ["int"]*3:
                raise ValueError("invalid native RM interface")
            result_type = Type("tuple", (("0",INT),("1",INT),("2",INT)))
            if fn["parameters"] != [("pc",dataclasses.asdict(INT))] or fn["output_type"] != dataclasses.asdict(result_type):
                raise ValueError("invalid native RM schema")

    def certificate(self):
        text = super().certificate().removesuffix("end Verified\n")
        program = self.artifact["native_program"]
        count = (len(program["instructions"]) + PAGE-1)//PAGE
        lines = [text, f"def native_tail_code_{count} : List Native.Instruction := []",
                 f"def native_tail_fetch_{count} (_ : Nat) : Native.Instruction := Native.halt",
                 f"theorem native_tail_correct_{count} (pc : Nat) (_ : {len(program['instructions'])} ≤ pc) :",
                 f"    native_tail_fetch_{count} pc = Native.select pc {len(program['instructions'])} native_tail_code_{count} := rfl"]
        for index in reversed(range(count)):
            base = index*PAGE
            code = program["instructions"][base:base+PAGE]
            end = base+len(code)
            name = f"native_page_{index}"
            lines += [f"def native_code_{index} : List Native.Instruction := " + lean_list(f"⟨{op}, {a}, {b}⟩" for op,a,b in code),
                f"def native_tail_code_{index} := native_code_{index} ++ native_tail_code_{index+1}",
                f"def native_tail_fetch_{index} (pc : Nat) : Native.Instruction :=",
                f"  if pc < {end} then Native.decode ({name}_graph.run (fun _ => (pc : Int))) else native_tail_fetch_{index+1} pc",
                f"theorem native_tail_correct_{index} (pc : Nat) (lower : {base} ≤ pc) :",
                f"    native_tail_fetch_{index} pc = Native.select pc {base} native_tail_code_{index} := by",
                f"  unfold native_tail_fetch_{index} native_tail_code_{index}",
                f"  rw [Native.select_append _ _ _ _ lower]",
                f"  change (if pc < {end} then _ else _) = (if pc < {end} then _ else _)",
                f"  by_cases upper : pc < {end}",
                f"  · simp only [upper, if_true]",
                f"    rw [{name}_correct]",
                f"    change Native.decode ((Native.lookupSource {base} native_code_{index}).run (fun _ => (pc : Int)) 3) = _",
                f"    rw [Native.lookup_correct, Native.decode_encode]",
                f"  · simp only [upper, if_false]",
                f"    exact native_tail_correct_{index+1} pc (by omega)"]
        lines += ["def native_program : Native.Program := " + lean_program(program, "native_tail_code_0"),
            "def native_fetch := native_tail_fetch_0",
            "theorem native_fetch_correct (pc : Nat) : native_fetch pc = Native.select pc 0 native_program.code :=",
            "  native_tail_correct_0 pc (Nat.zero_le pc)",
            "theorem native_step_correct (state : Native.State) :",
            "    Native.step native_program native_fetch state =",
            "      Native.step native_program (fun pc => Native.select pc 0 native_program.code) state :=",
            "  Native.step_correct _ _ native_fetch_correct state",
            "theorem native_execution_correct (state : Native.State) (actions : List Native.Action) :",
            "    Native.run native_program native_fetch state actions =",
            "      Native.run native_program (fun pc => Native.select pc 0 native_program.code) state actions :=",
            "  Native.execution_correct _ _ native_fetch_correct state actions",
            "#print axioms native_fetch_correct", "#print axioms native_step_correct",
            "#print axioms native_execution_correct", "end Verified", ""]
        return "\n".join(lines)

    def task(self, function, *arguments, source=False):
        cache = {}
        def fetch(pc):
            if pc not in cache:
                page = self.artifact["functions"].get(f"native_page_{pc//PAGE}")
                if page is None: return [15,0,0]
                graph = page["graph"]
                env = [pc]
                for term in graph["terms"]: env.append(evaluate(term, env))
                cache[pc] = [env[i] for i in graph["outputs"]]
            return cache[pc]
        return Machine(self.artifact["native_program"], function, arguments, None if source else fetch)

    def construct(self, class_name, *arguments):
        obj = Object(class_name)
        init = self.artifact["native_program"]["classes"][class_name].get("__init__")
        if init:
            task = self.task(init, obj, *arguments)
            result = task.run()
            if not isinstance(result, Finished): raise ValueError(f"constructor did not return: {result}")
            if result.value is not None: raise TypeError("__init__ must return None")
        elif arguments: raise TypeError("constructor takes no arguments")
        return obj


def compile_native(source, model_config=None):
    # A linear source instruction selector can be deeper than Python's default
    # recursion limit. This is a tooling limit, not a program-state bound.
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 20000))
    path = Path(source).resolve()
    raw = path.read_bytes()
    config = model_config or {}
    program = Frontend(raw.decode(), path, config.get("interfaces", {})).artifact()
    functions = [dict(name=f"native_page_{base//PAGE}", source=instruction_source(program["instructions"][base:base+PAGE], base),
        slots=["int"], inputs=1, output_sorts=["int"]*3, parameters=[("pc",INT)],
        output_type=Type("tuple", (("0",INT),("1",INT),("2",INT))))
        for base in range(0, len(program["instructions"]), PAGE)]
    bundle = make_bundle(path, hashlib.sha256(raw).hexdigest(), functions, config)
    bundle.artifact.update(format="zrth-verified-native-v1", native_program=program)
    return NativeBundle(bundle.artifact, bundle.modules, bundle.metadata)


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--config", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--proof", type=Path)
    parser.add_argument("--theorem", action="append", default=[])
    args = parser.parse_args()
    if bool(args.proof) != bool(args.theorem): parser.error("--proof and --theorem are required together")
    bundle = compile_native(args.source, json.loads(args.config.read_text()) if args.config else {})
    bundle.certify(args.out)
    if args.proof: bundle.check_properties(args.out, args.proof, args.theorem)
    print(f"Native source -> RM/object-machine translation checked: {args.out}")


if __name__ == "__main__": main()
