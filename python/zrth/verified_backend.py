"""Untrusted candidate emitter and certificate packaging for zrth.verified."""
from __future__ import annotations

import dataclasses
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def project_root():
    return Path(__file__).resolve().parents[2] / "verification" / "lean"


def provenance():
    project = project_root()
    paths = [project / "lean-toolchain", project / "lakefile.toml", project / "lake-manifest.json", project / "ReactiveModules.lean"]
    paths += sorted((project / "ReactiveModules").glob("*.lean"))
    paths += [Path(__file__).resolve(), Path(__file__).with_name("verified.py")]
    paths += [Path(__file__).with_name("verified_async.py"), Path(__file__).with_name("effects.py")]
    paths += [Path(__file__).with_name(name) for name in ("native_frontend.py", "native_runtime.py", "verified_native.py", "native_checks.py")]
    return {str(p.relative_to(project.parents[1])): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def audit_axioms(output):
    reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    if not reports:
        raise ValueError("Lean did not produce an axiom audit")
    for report in reports:
        names = {n.strip() for n in report.split(",") if n.strip()}
        if not names <= {"propext", "Classical.choice", "Quot.sound"}:
            raise ValueError(f"unapproved proof dependencies: {sorted(names)}")


def substitute(e, env):
    match e:
        case ["var", n]: return env.get(n, e)
        case ["lit" | "boolean", _]: return e
        case ["bin", op, a, b]: return ["bin", op, substitute(a, env), substitute(b, env)]
        case ["not", a]: return ["not", substitute(a, env)]
        case ["ite", c, a, b]: return ["ite", substitute(c, env), substitute(a, env), substitute(b, env)]
        case _: raise ValueError(f"invalid expression: {e}")


def candidate(s, env, next_):
    match s:
        case ["skip"]: return next_(env)
        case ["assignMany", slots, values]:
            if len(slots) != len(values): raise ValueError("assignment arity")
            return next_({**env, **dict(zip(slots, [substitute(v, env) for v in values]))})
        case ["ret", values]: return [substitute(v, env) for v in values]
        case ["seq", a, b]: return candidate(a, env, lambda env_: candidate(b, env_, next_))
        case ["branch", c, a, b]:
            left, right = candidate(a, env, next_), candidate(b, env, next_)
            if len(left) != len(right): raise ValueError("return arity differs by branch")
            return [["ite", substitute(c, env), x, y] for x, y in zip(left, right)]
        case ["call", targets, body]:
            def no_return(_): raise ValueError("every helper path must return")
            values = candidate(body, env, no_return)
            if len(values) != len(targets): raise ValueError("helper return arity")
            return next_({**env, **dict(zip(targets, values))})
        case ["forEach", slots, rows, body]:
            snapshot = [[substitute(v, env) for v in row] for row in rows]
            def iteration(index, current):
                if index == len(snapshot): return next_(current)
                return candidate(body, {**current, **dict(zip(slots, snapshot[index]))},
                                 lambda after: iteration(index + 1, after))
            return iteration(0, env)
        case _: raise ValueError(f"invalid source: {s}")


def evaluate(e, env):
    match e:
        case ["var", i]: return env[i]
        case ["lit" | "boolean", v]: return int(v)
        case ["not", a]: return int(not evaluate(a, env))
        case ["ite", c, a, b]: return evaluate(a if evaluate(c, env) else b, env)
        case ["bin", op, a, b]:
            x, y = evaluate(a, env), evaluate(b, env)
            return {"add": lambda: x + y, "sub": lambda: x - y, "eq": lambda: int(x == y),
                    "ne": lambda: int(x != y), "lt": lambda: int(x < y), "le": lambda: int(x <= y),
                    "gt": lambda: int(x > y), "ge": lambda: int(x >= y),
                    "and": lambda: int(bool(x) and bool(y)), "or": lambda: int(bool(x) or bool(y)),
                    "xor": lambda: int(bool(x) != bool(y))}[op]()
        case _: raise ValueError("unsupported graph operation")


def rm_graph(function):
    import torch
    import zrth

    inputs = [zrth.Var((zrth.Bool if t == "bool" else zrth.Int)([1, 1])) for t in function["slots"][:function["inputs"]]]
    outputs = [zrth.Var((zrth.Bool if t == "bool" else zrth.Int)([1, 1])) for t in function["output_sorts"]]
    terms, cache = [], {}
    op_names = dict(add="Add", sub="Sub", eq="Eq", ne="Ne", lt="Lt", le="Le", gt="Gt", ge="Ge", xor="Xor", **{"and": "And", "or": "Or"})

    def emit(e):
        key = json.dumps(e, separators=(",", ":"))
        if key in cache: return cache[key]
        match e:
            case ["var", n]:
                if not 0 <= n < len(inputs): raise ValueError("uninitialized local in candidate")
                return inputs[n]
            case ["lit", value]:
                if not -(2**63) <= value < 2**63:
                    raise ValueError("this RM adapter supports signed 64-bit literals; input arithmetic is mathematical")
                wire = zrth.Wire(zrth.Int([1, 1]))
                term = zrth.Term.constant(zrth.LIA.Int(torch.tensor([[value]], dtype=torch.int64)), [wire])
            case ["boolean", value]:
                wire = zrth.Wire(zrth.Bool([1, 1]))
                term = zrth.Term.constant(zrth.LIA.Bool(torch.tensor([[value]], dtype=torch.bool)), [wire])
            case ["bin", op, a, b]:
                reads = [emit(a), emit(b)]
                wire = zrth.Wire((zrth.Int if op in ("add", "sub") else zrth.Bool)([1, 1]))
                term = zrth.Term(getattr(zrth.LIA, op_names[op])(), [wire], reads)
            case ["not", a]:
                reads = [emit(a)]
                wire = zrth.Wire(zrth.Bool([1, 1]))
                term = zrth.Term(zrth.LIA.Not(), [wire], reads)
            case ["ite", c, a, b]:
                reads = [emit(c), emit(a), emit(b)]
                wire = zrth.Wire(reads[1].dtype)
                term = zrth.Term(zrth.LIA.Ite(), [wire], reads)
            case _: raise ValueError("invalid expression")
        cache[key] = wire
        terms.append(term)
        return wire

    def fallthrough(_): raise ValueError("every entrypoint path must return")
    lowered = candidate(function["source"], {}, fallthrough)
    if len(lowered) != len(outputs): raise ValueError("incorrect result layout")
    for out, expression in zip(outputs, lowered):
        wire = emit(expression)
        terms.append(zrth.Term(zrth.LIA.Id(), [zrth.X(out)], [wire]))
    module = zrth.Module(update=terms, vars=inputs + outputs)
    if len(module.atoms) != 1 or set(module.ctrl) != set(outputs):
        raise ValueError("unexpected RM module interface")
    index, graph = {wire: i for i, wire in enumerate(inputs)}, []
    # Read back actual module terms, not the candidate expression list.
    inverse = {"LIA_" + value: key for key, value in op_names.items()}
    for term in module.atoms[0].update:
        args = [["var", index[w]] for w in term.read]
        op = type(term.itype).__name__
        if len(term.write) != 1 or term.write[0] in index: raise ValueError("invalid RM write")
        match term.itype:
            case zrth.LIA.Int(t): expression = ["lit", int(t.item())]
            case zrth.LIA.Bool(t): expression = ["boolean", bool(t.item())]
            case zrth.LIA.Id(): expression = args[0]
            case zrth.LIA.Not(): expression = ["not", *args]
            case zrth.LIA.Ite(): expression = ["ite", *args]
            case _:
                if op not in inverse or len(args) != 2: raise ValueError(f"unsupported RM operator: {op}")
                expression = ["bin", inverse[op], *args]
        index[term.write[0]] = len(inputs) + len(graph)
        graph.append(expression)
    return module, dict(inputs=len(inputs), terms=graph, outputs=[index[zrth.X(w)] for w in outputs])


def lean_list(values): return "[" + ", ".join(values) + "]"


def lean_expr(e):
    match e:
        case ["lit", n] if type(n) is int: return f"(.lit ({n}))"
        case ["boolean", b] if type(b) is bool: return f"(.boolean {str(b).lower()})"
        case ["var", n] if type(n) is int and n >= 0: return f"(.var {n})"
        case ["bin", op, a, b] if op in {"add", "sub", "eq", "ne", "lt", "le", "gt", "ge", "and", "or", "xor"}:
            return f"(.bin .{op} {lean_expr(a)} {lean_expr(b)})"
        case ["not", a]: return f"(.not {lean_expr(a)})"
        case ["ite", c, a, b]: return f"(.ite {lean_expr(c)} {lean_expr(a)} {lean_expr(b)})"
        case _: raise ValueError("invalid expression")


def lean_source(s):
    match s:
        case ["skip"]: return ".skip"
        case ["assignMany", slots, values]: return f"(.assignMany {lean_list(map(str, slots))} {lean_list(map(lean_expr, values))})"
        case ["ret", values]: return f"(.ret {lean_list(map(lean_expr, values))})"
        case ["seq", a, b]: return f"(.seq {lean_source(a)} {lean_source(b)})"
        case ["branch", c, a, b]: return f"(.branch {lean_expr(c)} {lean_source(a)} {lean_source(b)})"
        case ["call", targets, body]: return f"(.call {lean_list(map(str, targets))} {lean_source(body)})"
        case ["forEach", slots, rows, body]:
            values = lean_list(lean_list(map(lean_expr, row)) for row in rows)
            return f"(.forEach {lean_list(map(str, slots))} {values} {lean_source(body)})"
        case _: raise ValueError("invalid source")


@dataclasses.dataclass
class VerificationBundle:
    artifact: dict
    modules: dict
    metadata: dict

    def run(self, entrypoint, *arguments):
        f = self.artifact["functions"][entrypoint]
        params = self.metadata[entrypoint]["parameters"]
        if len(arguments) != len(params): raise TypeError("wrong argument count")
        env = [v for (_, t), a in zip(params, arguments) for v in t.encode(a)]
        for term in f["graph"]["terms"]: env.append(evaluate(term, env))
        return [env[i] for i in f["graph"]["outputs"]]

    def certificate(self):
        lines = ["import ReactiveModules", "open ReactiveModules", "namespace Verified",
                 "set_option maxRecDepth 100000", "set_option maxHeartbeats 20000000"]
        for name, f in self.artifact["functions"].items():
            g = f["graph"]
            if type(g["inputs"]) is not int or g["inputs"] < 0 or any(type(i) is not int or i < 0 for i in g["outputs"]):
                raise ValueError("RM wire indices must be nonnegative integers")
            types = lean_list("." + t for t in f["slots"])
            ins = lean_list("." + t for t in f["slots"][:f["inputs"]])
            outs = lean_list("." + t for t in f["output_sorts"])
            lines += [f"def {name}_source : Source := {lean_source(f['source'])}",
                      f"def {name}_graph : Graph := ⟨{g['inputs']}, {lean_list(map(lean_expr, g['terms']))}, {lean_list(map(str, g['outputs']))}⟩",
                      f"theorem {name}_source_valid : validSource {name}_source {types} {outs} {f['inputs']} = true := by decide",
                      f"theorem {name}_graph_valid : validGraph {name}_graph {ins} {outs} = true := by decide",
                      f"theorem {name}_certificate : Certifies {name}_source {name}_graph := by unfold Certifies; decide",
                      f"theorem {name}_correct (env : Nat → Int) : {name}_graph.run env = {name}_source.run env {len(f['output_sorts'])} := certified_correct _ _ {name}_certificate env",
                      f"#print axioms {name}_correct"]
        return "\n".join(lines + ["end Verified", ""])

    def write(self, directory):
        path = Path(directory).resolve()
        path.mkdir(parents=True, exist_ok=True)
        (path / "status.json").write_text(json.dumps({"translation": "not-established", "properties": {}}) + "\n")
        (path / "Certificate.olean").unlink(missing_ok=True)
        current = hashlib.sha256(Path(self.artifact["source_path"]).read_bytes()).hexdigest()
        if current != self.artifact["source_sha256"]: raise ValueError("source changed; recompile")
        if provenance() != self.artifact["toolchain_sources"]: raise ValueError("verification tooling changed; recompile")
        self.validate_source()
        (path / "bundle.json").write_text(json.dumps(self.artifact, indent=2) + "\n")
        (path / "Certificate.lean").write_text(self.certificate())
        return path

    def validate_source(self):
        from .verified import Parser
        parser = Parser(Path(self.artifact["source_path"]).read_text(), self.artifact["source_path"])
        for name, f in self.artifact["functions"].items():
            parsed = parser.function(name)
            if any(f[k] != parsed[k] for k in ("source", "slots", "inputs", "output_sorts")):
                raise ValueError("source AST/schema differs from the trusted parser output")

    def certify(self, directory, lean_project=None):
        path = self.write(directory)
        project = Path(lean_project) if lean_project else project_root()
        subprocess.run(["lake", "build"], cwd=project, check=True)
        result = subprocess.run(["lake", "env", "lean", "--root=" + str(path), "-o", str(path / "Certificate.olean"), str(path / "Certificate.lean")],
                                cwd=project, text=True, capture_output=True)
        (path / "audit.log").write_text(result.stdout + result.stderr)
        if result.returncode:
            raise ValueError("Lean rejected the bundle:\n" + result.stdout + result.stderr)
        audit_axioms(result.stdout)
        if provenance() != self.artifact["toolchain_sources"]:
            raise ValueError("verification tooling changed during checking; recompile")
        if hashlib.sha256(Path(self.artifact["source_path"]).read_bytes()).hexdigest() != self.artifact["source_sha256"]:
            raise ValueError("source changed during checking; recompile")
        digest = lambda filename: hashlib.sha256((path / filename).read_bytes()).hexdigest()
        (path / "status.json").write_text(json.dumps(dict(translation="checked", properties={},
            bundle_sha256=digest("bundle.json"), certificate_sha256=digest("Certificate.lean"),
            checked_module_sha256=digest("Certificate.olean"),
            lean_version=subprocess.check_output(["lake", "env", "lean", "--version"], cwd=project, text=True).strip()), indent=2) + "\n")
        return path

    def check_properties(self, directory, proof, declarations):
        """Check named, explicitly authored Lean theorems against this exact bundle.

        A proved negation is a checked refutation, not a positive guarantee.
        The theorem's complete type is retained in the audit log.
        """
        path = Path(directory).resolve()
        status = json.loads((path / "status.json").read_text())
        invalid = {**status, "translation": "not-established",
                   "properties": {n: {"status": "not-established"} for n in status["properties"]}}
        (path / "status.json").write_text(json.dumps(invalid, indent=2) + "\n")
        if status["translation"] != "checked": raise ValueError("certify translation first")
        hashes = {"bundle.json": "bundle_sha256", "Certificate.lean": "certificate_sha256", "Certificate.olean": "checked_module_sha256"}
        for file, key in hashes.items():
            if hashlib.sha256((path / file).read_bytes()).hexdigest() != status[key]:
                raise ValueError(f"stale or tampered evidence: {file}")
        if json.dumps(self.artifact, indent=2) + "\n" != (path / "bundle.json").read_text():
            raise ValueError("in-memory artifact differs from checked bundle")
        if hashlib.sha256(Path(self.artifact["source_path"]).read_bytes()).hexdigest() != self.artifact["source_sha256"]:
            raise ValueError("source changed; recompile")
        if provenance() != self.artifact["toolchain_sources"]: raise ValueError("verification tooling changed; recompile")
        if not declarations or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", n) for n in declarations):
            raise ValueError("provide qualified Lean theorem identifiers")
        for name in declarations: status["properties"][name] = {"status": "not-established"}
        (path / "status.json").write_text(json.dumps(status, indent=2) + "\n")
        raw = Path(proof).read_text()
        suffix = "\n".join(
            f"run_cmd do\n  match ← Lean.getConstInfo ``{name} with\n"
            f"  | .thmInfo _ => pure ()\n  | _ => throwError \"expected a theorem declaration\"\n"
            f"#check {name}\n#print axioms {name}" for name in declarations)
        target = path / "Properties.lean"
        target.write_text(raw + "\n" + suffix + "\n")
        (path / "Properties.olean").unlink(missing_ok=True)
        env = dict(os.environ, LEAN_PATH=str(path) + os.pathsep + os.environ.get("LEAN_PATH", ""))
        result = subprocess.run(["lake", "env", "lean", "--root=" + str(path), "-o", str(path / "Properties.olean"), str(target)],
                                cwd=project_root(), env=env, text=True, capture_output=True)
        (path / "properties.log").write_text(result.stdout + result.stderr)
        if result.returncode: raise ValueError("Lean did not establish the requested properties:\n" + result.stdout + result.stderr)
        audit_axioms(result.stdout)
        for name in declarations:
            status["properties"][name] = dict(status="proved", proof_sha256=hashlib.sha256(raw.encode()).hexdigest(),
                                               audit="properties.log")
        (path / "status.json").write_text(json.dumps(status, indent=2) + "\n")
        return status


def make_bundle(path, digest, functions, model_config):
    artifact = dict(format="zrth-verified-handlers-v1", source_path=str(path), source_sha256=digest,
                    model_config=model_config, toolchain_sources=provenance(), functions={})
    modules, metadata = {}, {}
    for function in functions:
        name = function["name"]
        if not name.isascii() or not name.isidentifier(): raise ValueError("entrypoints need ASCII identifiers")
        module, graph = rm_graph(function)
        modules[name], metadata[name] = module, function
        artifact["functions"][name] = {k: v for k, v in function.items() if k not in ("parameters", "output_type")}
        artifact["functions"][name].update(graph=graph,
            parameters=[(n, dataclasses.asdict(t)) for n, t in function["parameters"]],
            output_type=dataclasses.asdict(function["output_type"]))
    return VerificationBundle(artifact, modules, metadata)
