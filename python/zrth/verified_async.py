"""Typed async Request handlers -> RM segments -> checked heap/resumption model.

The trusted frontend recognizes top-level await Request boundaries and lays out
frames. Lean checks every RM segment and their composition with the declared
source coroutine and heap model. This is not a CPython/asyncio compiler proof.
"""
from __future__ import annotations

import ast
import dataclasses
import hashlib
from pathlib import Path

from .effects import Heap, Operation, Request, Task
from .verified import INT, Parser, Type, UnsupportedPython, seq
from .verified_backend import VerificationBundle, evaluate, make_bundle


OPERATIONS = dict(zip(Operation, (
    "newDict", "newSet", "dictSet", "dictGet", "dictContains", "dictLen", "dictDelete",
    "dictCopy", "dictKeyAt", "setAdd", "setDiscard", "setContains", "setLen", "setRemove",
    "setCopy", "dictItem", "dictClear", "setClear"), strict=True))


class AsyncParser(Parser):
    def __init__(self, source, filename):
        self.filename = str(filename)
        tree = ast.parse(source, filename=self.filename)
        # Validate Python scope/syntax rules too, without executing the code.
        compile(source, self.filename, "exec")
        self.async_functions, self.effect_names = {}, {}
        self.operation_name = self.request_name = None
        normal = []
        for node in tree.body:
            if isinstance(node, ast.ImportFrom) and node.module == "zrth.effects":
                if node.level:
                    self.fail(node, "effect imports must be absolute")
                for alias in node.names:
                    if alias.name not in {"Operation", "Request"}:
                        self.fail(node, "only Operation and Request may be imported from zrth.effects")
                    name = alias.asname or alias.name
                    if name in self.effect_names or alias.name in self.effect_names.values():
                        self.fail(node, "duplicate effect import")
                    self.effect_names[name] = alias.name
                    if alias.name == "Operation": self.operation_name = name
                    else: self.request_name = name
            elif isinstance(node, ast.AsyncFunctionDef):
                if node.name in self.async_functions:
                    self.fail(node, "duplicate async function")
                self.async_functions[node.name] = node
            else:
                normal.append(node)
        super().__init__(source, filename, tree=ast.Module(body=normal, type_ignores=[]))
        for name in self.effect_names:
            if name in self.types or name in self.functions or name in self.async_functions or name in {"len", "tuple", "dataclass", "Enum"}:
                self.fail(tree, "effect imports cannot shadow declarations or builtins")
        for name, fn in self.async_functions.items():
            if name in self.functions or name in self.types or name in {"len", "tuple", "dataclass", "Enum"}:
                self.fail(fn, "duplicate or shadowing async declaration")
            self.check_signature(fn)
            if fn.args.kw_defaults:
                self.fail(fn, "async defaults are unsupported")
            for arg in fn.args.args:
                self.annotation(arg.annotation)
            self.annotation(fn.returns)

    def reserved(self, name):
        return super().reserved(name) or name in self.effect_names or name in self.async_functions

    def request(self, node):
        call = node.value
        if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Name) and call.func.id == self.request_name):
            self.fail(node, "await requires the declared Request interface; async helper calls are not lowered yet")
        if not 1 <= len(call.args) <= 4:
            self.fail(call, "Request requires an explicit Operation member and up to three integer fields")
        operation = call.args[0]
        if not (isinstance(operation, ast.Attribute) and isinstance(operation.value, ast.Name)
                and operation.value.id == self.operation_name and operation.attr in Operation.__members__):
            self.fail(operation, "Request operation must be a literal imported Operation member")
        names = ("reference", "key", "value")
        supplied = dict(zip(names, call.args[1:]))
        for kw in call.keywords:
            if kw.arg not in names or kw.arg in supplied:
                self.fail(kw, "unknown, duplicate, or unpacked Request field")
            supplied[kw.arg] = kw.value
        # Evaluate arguments in Python's order, then reorder their pure results.
        parsed = {}
        for name, expression in supplied.items():
            parsed[name] = self.coerce(self.expression(expression, set(), INT), INT, expression)
        args = [parsed[name].terms[0] if name in parsed else ["lit", 0] for name in names]
        return Operation[operation.attr], args

    def coroutine(self, name):
        if name not in self.async_functions:
            raise UnsupportedPython(f"no async function {name!r} in {self.filename}")
        self.fn = self.async_functions[name]
        output = self.annotation(self.fn.returns)
        frame = []
        for arg in self.fn.args.args:
            if self.reserved(arg.arg) or arg.arg in dict(frame):
                self.fail(arg, "duplicate parameter or reserved-name shadowing")
            frame.append((arg.arg, self.annotation(arg.annotation)))
        body = list(self.fn.body)
        if not body or not isinstance(body[-1], ast.Return):
            self.fail(self.fn, "coroutines require a final top-level return")
        if isinstance(body[-1].value, ast.Await):
            used = {n.id for n in ast.walk(self.fn) if isinstance(n, ast.Name)} | set(dict(frame))
            temp = "_await_result"
            while temp in used: temp += "_"
            node = body.pop()
            body += [ast.copy_location(ast.Assign(targets=[ast.Name(id=temp, ctx=ast.Store())], value=node.value), node),
                     ast.copy_location(ast.Return(value=ast.Name(id=temp, ctx=ast.Load())), node)]
        chunks, pending = [], []
        for index, node in enumerate(body):
            value = node.value if isinstance(node, (ast.Assign, ast.AnnAssign, ast.Expr)) else None
            if isinstance(value, ast.Await):
                target = None
                if isinstance(node, (ast.Assign, ast.AnnAssign)):
                    if isinstance(node, ast.Assign) and len(node.targets) != 1:
                        self.fail(node, "await assignment requires one local name")
                    destination = node.target if isinstance(node, ast.AnnAssign) else node.targets[0]
                    if not isinstance(destination, ast.Name) or self.reserved(destination.id):
                        self.fail(destination, "await assignment requires one nonreserved local name")
                    if isinstance(node, ast.AnnAssign) and self.annotation(node.annotation) != INT:
                        self.fail(node, "Request replies are exact integers")
                    target = destination.id
                chunks.append((pending, value, target))
                pending = []
            else:
                for child in ast.walk(node):
                    if isinstance(child, ast.Await):
                        self.fail(child, "await inside an expression, branch, or loop is not supported yet")
                    if isinstance(child, ast.Return) and not (child is node and index == len(body) - 1):
                        self.fail(child, "early coroutine returns are unsupported; use a pure helper")
                pending.append(node)
        chunks.append((pending, None, None))
        functions, stages = [], []
        previous_target = None
        for index, (statements, suspension, target) in enumerate(chunks):
            self.bindings, self.slots, self.parameters = {}, [], []
            self.pending, self.call_stack, self.output = [], [name], output
            for local, typ in frame:
                self.bindings[local] = self.allocate(typ)
                self.parameters.append((local, typ))
            if index:
                reply = self.allocate(INT)
                self.parameters.append(("__effect_response__", INT))
                if previous_target:
                    if previous_target in self.bindings and self.bindings[previous_target].type != INT:
                        self.fail(self.fn, "await cannot change the type of an existing local")
                    self.bindings[previous_target] = reply
            inputs = len(self.slots)
            source = self.block(statements, set())
            if suspension:
                operation, args = self.request(suspension)
                frame = [(local, binding.type) for local, binding in self.bindings.items()]
                values = args + [term for binding in self.bindings.values() for term in binding.terms]
                result_type = Type("tuple", tuple((str(i), typ) for i, typ in enumerate([INT, INT, INT] + [t for _, t in frame])))
                source = seq([source, *self.pending, ["ret", values]])
                effect = operation.name
            else:
                result_type, effect = output, None
            stage_name = f"{name}_stage_{index}"
            functions.append(dict(name=stage_name, source=source, slots=list(self.slots), inputs=inputs,
                                  output_sorts=result_type.sorts, parameters=list(self.parameters), output_type=result_type))
            stages.append(dict(name=stage_name, effect=effect))
            previous_target = target
        return functions, dict(entrypoint=name, stages=stages)


class CoroutineBundle(VerificationBundle):
    def validate_source(self):
        parser = AsyncParser(Path(self.artifact["source_path"]).read_text(), self.artifact["source_path"])
        functions, control = parser.coroutine(self.artifact["coroutine"]["entrypoint"])
        if control != self.artifact["coroutine"] or set(self.artifact["functions"]) != {f["name"] for f in functions}:
            raise ValueError("coroutine boundaries differ from the trusted parser output")
        for function in functions:
            saved = self.artifact["functions"][function["name"]]
            expected = {k: v for k, v in function.items() if k not in ("parameters", "output_type")}
            expected.update(parameters=[(n, dataclasses.asdict(t)) for n, t in function["parameters"]],
                            output_type=dataclasses.asdict(function["output_type"]))
            if any(saved[k] != value for k, value in expected.items()):
                raise ValueError("coroutine source AST/schema differs from the trusted parser output")

    def certificate(self):
        text = super().certificate().removesuffix("end Verified\n")
        stages = self.artifact["coroutine"]["stages"]
        blocks, proofs, interfaces = [], [], []
        for stage in stages:
            name = stage["name"]
            count = len(self.artifact["functions"][name]["output_sorts"])
            effect = "none" if stage["effect"] is None else "some ." + OPERATIONS[Operation[stage["effect"]]]
            blocks.append(f"⟨{name}_source, {name}_graph, {count}, {effect}⟩")
            proofs.append(f"  · exact {name}_correct env")
            function = self.artifact["functions"][name]
            ins = "[" + ", ".join("." + t for t in function["slots"][:function["inputs"]]) + "]"
            outs = "[" + ", ".join("." + t for t in function["output_sorts"]) + "]"
            interfaces.append(f"⟨{ins}, {outs}, {str(stage['effect'] is not None).lower()}⟩")
        lines = [text, "def coroutine_interfaces : List Coroutine.Interface := [" + ", ".join(interfaces) + "]",
                 "theorem coroutine_frames_valid : Coroutine.validFrames coroutine_interfaces = true := by decide",
                 "def coroutine_blocks : List Coroutine.Block := [" + ", ".join(blocks) + "]",
                 "theorem coroutine_blocks_correct : Coroutine.Correct coroutine_blocks := by",
                 "  intro block member env",
                 "  simp only [coroutine_blocks, List.mem_cons, List.not_mem_nil, or_false] at member",
                 "  rcases member with " + " | ".join("rfl" for _ in stages), *proofs,
                 "theorem coroutine_segment_correct (frame : Coroutine.Frame) :",
                 "    Coroutine.compiledSegment coroutine_blocks frame = Coroutine.sourceSegment coroutine_blocks frame :=",
                 "  Coroutine.segment_correct _ coroutine_blocks_correct frame",
                 "theorem coroutine_start_correct (owner : Nat) (args : List Int) :",
                 "    Coroutine.initial (Coroutine.compiledSegment coroutine_blocks) owner args =",
                 "      Coroutine.initial (Coroutine.sourceSegment coroutine_blocks) owner args :=",
                 "  Coroutine.initial_correct _ coroutine_blocks_correct owner args",
                 "theorem coroutine_serve_correct (heap : Heap.Store) (machine : Coroutine.State) (ticket : Effects.Ticket) :",
                 "    Effects.serve (Coroutine.compiledSegment coroutine_blocks) heap machine ticket =",
                 "      Effects.serve (Coroutine.sourceSegment coroutine_blocks) heap machine ticket :=",
                 "  Coroutine.serve_correct _ coroutine_blocks_correct heap machine ticket",
                 "theorem coroutine_execution_correct (heap : Heap.Store) (machine : Coroutine.State) (tickets : List Effects.Ticket) :",
                 "    Coroutine.runTickets (Coroutine.compiledSegment coroutine_blocks) heap machine tickets =",
                 "      Coroutine.runTickets (Coroutine.sourceSegment coroutine_blocks) heap machine tickets :=",
                 "  Coroutine.execution_correct _ coroutine_blocks_correct heap machine tickets",
                 "#print axioms coroutine_segment_correct", "#print axioms coroutine_start_correct",
                 "#print axioms coroutine_serve_correct", "#print axioms coroutine_execution_correct", "end Verified", ""]
        return "\n".join(lines)

    def task(self, *arguments):
        """Execute exported RM graphs, suspending at each certified boundary.

        Like synchronous bundle.run, the final result is a flat scalar list.
        The runtime adapter/Python heap remain tested trust boundaries.
        """
        stages = self.artifact["coroutine"]["stages"]
        parameters = self.metadata[stages[0]["name"]]["parameters"]
        if len(arguments) != len(parameters): raise TypeError("wrong argument count")
        encoded = [v for (_, typ), arg in zip(parameters, arguments) for v in typ.encode(arg)]

        async def execute():
            values = encoded
            for stage in stages:
                graph = self.artifact["functions"][stage["name"]]["graph"]
                if len(values) != graph["inputs"]:
                    raise ValueError("coroutine frame layout differs from RM inputs")
                env = list(values)
                for term in graph["terms"]: env.append(evaluate(term, env))
                outputs = [env[i] for i in graph["outputs"]]
                if stage["effect"] is None:
                    return outputs
                response = await Request(Operation[stage["effect"]], *outputs[:3])
                values = outputs[3:] + [response]
            raise ValueError("coroutine is missing a return segment")
        return Task(execute())

    def run(self, *arguments, heap=None):
        from .effects import Pending, Failed
        task = self.task(*arguments)
        heap = Heap() if heap is None else heap
        try:
            result = task.start()
            while isinstance(result, Pending): result = task.serve(result, heap)
            if isinstance(result, Failed): raise result.error
            return result.value
        finally:
            task.close()


def compile_coroutine(source, entrypoint, model_config=None):
    path = Path(source).resolve()
    raw = path.read_bytes()
    functions, control = AsyncParser(raw.decode("utf-8"), path).coroutine(entrypoint)
    bundle = make_bundle(path, hashlib.sha256(raw).hexdigest(), functions, model_config or {})
    bundle.artifact.update(format="zrth-verified-coroutine-v1", coroutine=control)
    return CoroutineBundle(bundle.artifact, bundle.modules, bundle.metadata)


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--entrypoint", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--proof", type=Path)
    parser.add_argument("--theorem", action="append", default=[])
    args = parser.parse_args()
    if bool(args.proof) != bool(args.theorem): parser.error("--proof and --theorem must be supplied together")
    bundle = compile_coroutine(args.source, args.entrypoint)
    bundle.certify(args.out)
    if args.proof: bundle.check_properties(args.out, args.proof, args.theorem)
    print(f"RM segments and heap/resumption composition checked. Evidence: {args.out}")


if __name__ == "__main__":
    main()
