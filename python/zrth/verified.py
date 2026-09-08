"""Typed, effect-explicit Python -> actual RM -> Lean-checked translation.

The parser/schema resolver is trusted. The candidate compiler and RM exporter
are not: Lean checks source well-formedness and equality to a proved lowering.
No source module is imported or executed by this frontend.
"""
from __future__ import annotations

import ast
import dataclasses
import hashlib
import json
from pathlib import Path


class UnsupportedPython(ValueError):
    pass


@dataclasses.dataclass(frozen=True)
class Type:
    name: str
    fields: tuple[tuple[str, "Type"], ...] = ()
    members: tuple[tuple[str, int], ...] = ()
    optional: "Type | None" = None

    @property
    def sorts(self):
        if self.optional:
            return ["bool"] + self.optional.sorts
        if self.fields:
            return [s for _, field in self.fields for s in field.sorts]
        return ["bool" if self.name == "bool" else "int"]

    def zero(self):
        return [["boolean", False] if s == "bool" else ["lit", 0] for s in self.sorts]

    def encode(self, value):
        if self.optional:
            return [0] + [0] * len(self.optional.sorts) if value is None else [1] + self.optional.encode(value)
        if self.fields:
            result = []
            for name, field in self.fields:
                item = value[int(name)] if self.name == "tuple" else getattr(value, name)
                result += field.encode(item)
            return result
        if self.members:
            if type(value).__name__ != self.name or value.name not in dict(self.members):
                raise TypeError(f"expected {self.name}")
            return [dict(self.members)[value.name]]
        if type(value) is not (bool if self.name == "bool" else int):
            raise TypeError(f"expected exact {self.name}, got {type(value).__name__}")
        return [int(value)]


INT, BOOL = Type("int"), Type("bool")


@dataclasses.dataclass
class Value:
    type: Type
    terms: list


def seq(items):
    result = ["skip"]
    for item in reversed(items):
        result = ["seq", item, result]
    return result


class Parser:
    def __init__(self, source, filename):
        self.source, self.filename = source, str(filename)
        self.tree = ast.parse(source, filename=self.filename)
        self.types = {"int": INT, "bool": BOOL}
        self.functions = {}
        imports = set()
        for node in self.tree.body:
            if isinstance(node, ast.ImportFrom):
                permitted = {"dataclasses": {"dataclass"}, "enum": {"Enum"}, "__future__": {"annotations"}}
                if node.level or node.module not in permitted or any(
                    a.name not in permitted[node.module] or a.asname for a in node.names
                ):
                    self.fail(node, "only dataclass, Enum and future annotations imports are supported")
                imports.update(a.name for a in node.names)
            elif isinstance(node, ast.ClassDef):
                self.record(node, imports)
            elif isinstance(node, ast.FunctionDef):
                if node.name in self.functions or node.name in self.types or node.name in {"tuple", "Enum", "dataclass"}:
                    self.fail(node, "duplicate or shadowing declaration")
                if node.decorator_list or node.args.defaults or node.args.kw_defaults:
                    self.fail(node, "decorators and function defaults may execute code at module load")
                for arg in node.args.posonlyargs + node.args.args + node.args.kwonlyargs:
                    self.annotation(arg.annotation)
                self.annotation(node.returns)
                self.functions[node.name] = node
            elif not self.docstring(node):
                self.fail(node, "unsupported module statement")

    def fail(self, node, message):
        raise UnsupportedPython(f"{self.filename}:{getattr(node, 'lineno', 1)}:{getattr(node, 'col_offset', 0) + 1}: {message}")

    @staticmethod
    def docstring(node):
        return isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str)

    def annotation(self, node):
        if isinstance(node, ast.Name) and node.id in self.types:
            return self.types[node.id]
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            if isinstance(node.right, ast.Constant) and node.right.value is None:
                inner = self.annotation(node.left)
                return Type(inner.name + " | None", optional=inner)
        if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id == "tuple":
            items = node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
            return Type("tuple", tuple((str(i), self.annotation(t)) for i, t in enumerate(items)))
        self.fail(node, "expected int, bool, declared immutable record/enum, optional, or fixed tuple type")

    def record(self, node, imports):
        if node.name in self.types or node.name in self.functions or node.name in {"tuple", "Enum", "dataclass"} or node.keywords:
            self.fail(node, "duplicate or unsupported class declaration")
        body = [n for n in node.body if not self.docstring(n)]
        if len(node.bases) == 1 and isinstance(node.bases[0], ast.Name) and node.bases[0].id == "Enum":
            if "Enum" not in imports or node.decorator_list:
                self.fail(node, "Enum must be imported and undecorated")
            members = []
            for member in body:
                if not (isinstance(member, ast.Assign) and len(member.targets) == 1 and
                        isinstance(member.targets[0], ast.Name) and isinstance(member.value, ast.Constant) and
                        type(member.value.value) is int):
                    self.fail(member, "enum members must be distinct integer literals")
                members.append((member.targets[0].id, member.value.value))
                if member.targets[0].id.startswith("_"):
                    self.fail(member, "private and special enum members are unsupported")
            if not members or len({n for n, _ in members}) != len(members) or len({v for _, v in members}) != len(members):
                self.fail(node, "empty enums and enum aliases are unsupported")
            self.types[node.name] = Type(node.name, members=tuple(members))
            return
        decorators = node.decorator_list
        if node.bases or "dataclass" not in imports or len(decorators) != 1:
            self.fail(node, "records must be @dataclass(frozen=True), without inheritance")
        dec = decorators[0]
        if not (isinstance(dec, ast.Call) and isinstance(dec.func, ast.Name) and dec.func.id == "dataclass"
                and not dec.args and len(dec.keywords) == 1 and dec.keywords[0].arg == "frozen"
                and isinstance(dec.keywords[0].value, ast.Constant) and dec.keywords[0].value.value is True):
            self.fail(dec, "records must be @dataclass(frozen=True)")
        fields = []
        for field in body:
            if not isinstance(field, ast.AnnAssign) or not isinstance(field.target, ast.Name) or field.value is not None:
                self.fail(field, "record fields require annotations and no defaults or methods")
            if field.target.id.startswith("_"):
                self.fail(field, "private and special record fields are unsupported")
            fields.append((field.target.id, self.annotation(field.annotation)))
        if not fields or len({n for n, _ in fields}) != len(fields):
            self.fail(node, "records must have distinct fields")
        self.types[node.name] = Type(node.name, fields=tuple(fields))

    def function(self, name):
        if name not in self.functions:
            raise UnsupportedPython(f"no function {name!r} in {self.filename}")
        self.fn = self.functions[name]
        args = self.fn.args
        if self.fn.decorator_list or args.posonlyargs or args.kwonlyargs or args.vararg or args.kwarg or args.defaults:
            self.fail(self.fn, "entrypoints require undecorated, annotated positional parameters without defaults")
        self.bindings, self.slots, self.parameters = {}, [], []
        for arg in args.args:
            typ = self.annotation(arg.annotation)
            if arg.arg in self.bindings or arg.arg in self.types:
                self.fail(arg, "duplicate parameter or type-name shadowing")
            self.bindings[arg.arg] = self.allocate(typ)
            self.parameters.append((arg.arg, typ))
        input_count = len(self.slots)
        self.output = self.annotation(self.fn.returns)
        program = self.block(self.fn.body, set())
        return dict(name=name, source=program, slots=list(self.slots), inputs=input_count,
                    output_sorts=self.output.sorts, parameters=self.parameters, output_type=self.output)

    def allocate(self, typ):
        first = len(self.slots)
        self.slots.extend(typ.sorts)
        return Value(typ, [["var", first + i] for i in range(len(typ.sorts))])

    def path(self, node):
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            return self.path(node.value) + "." + node.attr
        return ""

    def refinement(self, node, truth):
        if isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.comparators[0], ast.Constant) and node.comparators[0].value is None:
            if (isinstance(node.ops[0], ast.IsNot) and truth) or (isinstance(node.ops[0], ast.Is) and not truth):
                return {self.path(node.left)}
        if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And) and truth:
            return set().union(*(self.refinement(v, True) for v in node.values))
        return set()

    def expression(self, node, narrowed, expected=None):
        if isinstance(node, ast.Constant):
            if node.value is None and expected and expected.optional:
                return Value(expected, expected.zero())
            if type(node.value) in (bool, int):
                return Value(BOOL if type(node.value) is bool else INT,
                             [["boolean", node.value] if type(node.value) is bool else ["lit", node.value]])
        elif isinstance(node, ast.Name) and node.id in self.bindings:
            return self.bindings[node.id]
        elif isinstance(node, ast.Attribute):
            if isinstance(node.value, ast.Name) and node.value.id in self.types:
                typ = self.types[node.value.id]
                if node.attr in dict(typ.members):
                    return Value(typ, [["lit", dict(typ.members)[node.attr]]])
            parent = self.expression(node.value, narrowed)
            if parent.type.optional:
                if self.path(node.value) not in narrowed:
                    self.fail(node, "optional field access requires an explicit is-not-None branch")
                parent = Value(parent.type.optional, parent.terms[1:])
            start = 0
            for field, typ in parent.type.fields:
                if field == node.attr:
                    return Value(typ, parent.terms[start:start + len(typ.sorts)])
                start += len(typ.sorts)
        elif isinstance(node, ast.Tuple):
            expected_fields = expected.fields if expected and expected.name == "tuple" else ()
            values = [self.coerce(self.expression(n, narrowed, expected_fields[i][1] if i < len(expected_fields) else None),
                                  expected_fields[i][1], n) if i < len(expected_fields) else self.expression(n, narrowed)
                      for i, n in enumerate(node.elts)]
            return Value(Type("tuple", tuple((str(i), v.type) for i, v in enumerate(values))), [e for v in values for e in v.terms])
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in self.types:
            typ = self.types[node.func.id]
            if not typ.fields or typ.name == "tuple" or len(node.args) > len(typ.fields):
                self.fail(node, "only immutable record constructors are supported calls")
            supplied = {field: value for (field, _), value in zip(typ.fields, node.args)}
            for kw in node.keywords:
                if kw.arg not in dict(typ.fields) or kw.arg in supplied:
                    self.fail(kw, "unknown or duplicate constructor argument")
                supplied[kw.arg] = kw.value
            if set(supplied) != set(dict(typ.fields)):
                self.fail(node, "all record fields must be supplied")
            values = [self.coerce(self.expression(supplied[f], narrowed, t), t, supplied[f]) for f, t in typ.fields]
            return Value(typ, [e for v in values for e in v.terms])
        elif isinstance(node, ast.UnaryOp):
            value = self.expression(node.operand, narrowed)
            if isinstance(node.op, ast.Not) and value.type == BOOL:
                return Value(BOOL, [["not", value.terms[0]]])
            if isinstance(node.op, ast.USub) and value.type == INT:
                return Value(INT, [["bin", "sub", ["lit", 0], value.terms[0]]])
        elif isinstance(node, ast.BinOp) and type(node.op) in (ast.Add, ast.Sub):
            a, b = self.expression(node.left, narrowed), self.expression(node.right, narrowed)
            if a.type == b.type == INT:
                return Value(INT, [["bin", "add" if isinstance(node.op, ast.Add) else "sub", a.terms[0], b.terms[0]]])
        elif isinstance(node, ast.BoolOp):
            terms, context = [], set(narrowed)
            for value in node.values:
                parsed = self.expression(value, context)
                if parsed.type != BOOL:
                    self.fail(value, "and/or require Boolean operands")
                terms.append(parsed.terms[0])
                context |= self.refinement(value, isinstance(node.op, ast.And))
            result = terms[-1]
            for term in reversed(terms[:-1]):
                result = ["bin", "and" if isinstance(node.op, ast.And) else "or", term, result]
            return Value(BOOL, [result])
        elif isinstance(node, ast.Compare) and len(node.ops) == 1:
            a = self.expression(node.left, narrowed)
            other = node.comparators[0]
            if isinstance(other, ast.Constant) and other.value is None and a.type.optional and isinstance(node.ops[0], (ast.Is, ast.IsNot)):
                return Value(BOOL, [a.terms[0] if isinstance(node.ops[0], ast.IsNot) else ["not", a.terms[0]]])
            b = self.expression(other, narrowed)
            names = {ast.Eq: "eq", ast.NotEq: "ne", ast.Lt: "lt", ast.LtE: "le", ast.Gt: "gt", ast.GtE: "ge"}
            op = names.get(type(node.ops[0]))
            if op and a.type == b.type and not a.type.fields and not a.type.optional:
                if op not in ("eq", "ne") and a.type != INT:
                    self.fail(node, "ordering comparisons require integers")
                return Value(BOOL, [["bin", op, a.terms[0], b.terms[0]]])
        elif isinstance(node, ast.IfExp):
            c = self.expression(node.test, narrowed)
            if c.type != BOOL:
                self.fail(node.test, "conditions must be Boolean")
            a = self.expression(node.body, narrowed | self.refinement(node.test, True), expected)
            b = self.expression(node.orelse, narrowed | self.refinement(node.test, False), expected)
            if a.type == b.type:
                return Value(a.type, [["ite", c.terms[0], x, y] for x, y in zip(a.terms, b.terms)])
        self.fail(node, "unsupported expression, unsafe access, or incompatible operand types")

    def coerce(self, value, expected, node):
        if value.type == expected:
            return value
        if expected.optional == value.type:
            return Value(expected, [["boolean", True]] + value.terms)
        self.fail(node, f"expected {expected.name}, got {value.type.name}")

    def block(self, body, narrowed):
        statements = []
        for node in body:
            if self.docstring(node) or isinstance(node, ast.Pass):
                continue
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                if isinstance(node, ast.Assign) and len(node.targets) != 1:
                    self.fail(node, "chained assignments are unsupported")
                target = node.target if isinstance(node, ast.AnnAssign) else node.targets[0]
                if not isinstance(target, ast.Name) or target.id in self.types:
                    self.fail(target, "only local name assignment is supported; records are immutable")
                expected = self.annotation(node.annotation) if isinstance(node, ast.AnnAssign) else (
                    self.bindings[target.id].type if target.id in self.bindings else None)
                value = self.expression(node.value, narrowed, expected)
                if expected:
                    value = self.coerce(value, expected, node)
                if target.id not in self.bindings:
                    self.bindings[target.id] = self.allocate(value.type)
                binding = self.bindings[target.id]
                self.coerce(value, binding.type, node)
                statements.append(["assignMany", [e[1] for e in binding.terms], value.terms])
                narrowed = {p for p in narrowed if p != target.id and not p.startswith(target.id + ".")}
            elif isinstance(node, ast.If):
                condition = self.expression(node.test, narrowed)
                if condition.type != BOOL:
                    self.fail(node.test, "conditions must be Boolean")
                statements.append(["branch", condition.terms[0],
                    self.block(node.body, narrowed | self.refinement(node.test, True)),
                    self.block(node.orelse, narrowed | self.refinement(node.test, False))])
                # Do not carry speculative optional refinements beyond a branch.
                narrowed = set()
            elif isinstance(node, ast.Return):
                result = self.coerce(self.expression(node.value, narrowed, self.output), self.output, node)
                statements.append(["ret", result.terms])
            else:
                self.fail(node, "unsupported statement (including effects, loops, async, exceptions and mutation)")
        return seq(statements)


def compile_module(source, entrypoints, model_config=None):
    """Compile without importing user code. Certification is an explicit later step.

    source is a filesystem path; entrypoints is a sequence of function names.
    model_config is provenance/assumptions, never code or algorithm rewrites.
    """
    from .verified_backend import make_bundle
    path = Path(source).resolve()
    raw = path.read_bytes()
    parser = Parser(raw.decode("utf-8"), path)
    if not entrypoints or len(set(entrypoints)) != len(entrypoints):
        raise ValueError("provide distinct entrypoints")
    functions = [parser.function(name) for name in entrypoints]
    return make_bundle(path, hashlib.sha256(raw).hexdigest(), functions, model_config or {})


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--entrypoint", action="append", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--config", type=Path)
    parser.add_argument("--proof", type=Path)
    parser.add_argument("--theorem", action="append", default=[])
    args = parser.parse_args()
    if bool(args.proof) != bool(args.theorem): parser.error("--proof and --theorem must be supplied together")
    bundle = compile_module(args.source, args.entrypoint, json.loads(args.config.read_text()) if args.config else {})
    bundle.certify(args.out)
    if args.proof:
        bundle.check_properties(args.out, args.proof, args.theorem)
    print(f"Translation checked. {len(args.theorem)} property theorem(s) checked. Evidence: {args.out}")


if __name__ == "__main__":
    main()
