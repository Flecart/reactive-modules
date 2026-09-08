"""Fail-closed Python object/async frontend. No source module is executed.

The instruction tape is the elaborated source model. Names, literals and call
sites are data; no protocol names or source hashes occur in the lowering.
"""
from __future__ import annotations

import ast
from pathlib import Path

from .verified import UnsupportedPython


OPS = ("const", "load", "store", "pop", "dup", "dup2", "attr", "setattr", "item",
       "setitem", "binary", "unary", "build", "call", "await", "return", "jump",
       "branch", "unpack", "format", "join", "raise", "global", "iter", "next",
       "delitem", "swap")
BUILTINS = {"dict", "set", "list", "tuple", "len", "max", "min", "range", "print",
            "str", "repr", "bool", "int", "KeyError", "IndexError", "ValueError",
            "TypeError", "RuntimeError", "ZeroDivisionError"}
BINARY = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul", ast.FloorDiv: "floordiv",
          ast.Mod: "mod", ast.Eq: "eq", ast.NotEq: "ne", ast.Lt: "lt", ast.LtE: "le",
          ast.Gt: "gt", ast.GtE: "ge", ast.Is: "is", ast.IsNot: "isnot",
          ast.In: "in", ast.NotIn: "notin"}


class Frontend:
    def __init__(self, source, filename, interfaces=None):
        self.filename = str(filename)
        self.interfaces = interfaces or {}
        self.tree = ast.parse(source, filename=self.filename)
        compile(source, self.filename, "exec")  # syntax/scope validation, never exec
        self.pool, self.code, self.locations, self.functions, self.classes = [], [], [], {}, {}
        self.imports, self.declarations = {}, []
        for node in self.tree.body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                for alias in node.names:
                    if alias.name == "*": self.fail(node, "wildcard imports are unsupported")
                    module = ("." * node.level + (node.module or "")) if isinstance(node, ast.ImportFrom) else ""
                    name = alias.asname or (alias.name if module else alias.name.split(".")[0])
                    if name in self.imports: self.fail(node, "duplicate import binding")
                    self.imports[name] = module + "." + alias.name if module else alias.name
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self.declarations.append((node.name, node))
            elif isinstance(node, ast.ClassDef):
                if node.bases or node.keywords or node.decorator_list:
                    self.fail(node, "native classes require plain method-only declarations")
                self.classes[node.name] = {}
                for member in node.body:
                    if isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        if member.name.startswith("__") and member.name != "__init__":
                            self.fail(member, "custom Python data-model methods are outside the object profile")
                        if member.name == "__init__" and isinstance(member, ast.AsyncFunctionDef):
                            self.fail(member, "Python constructors must be synchronous")
                        self.declarations.append((node.name + "." + member.name, member))
                        self.classes[node.name][member.name] = node.name + "." + member.name
                    elif not self.doc(member) and not isinstance(member, ast.Pass):
                        self.fail(member, "class body must contain methods only")
            elif not self.doc(node): self.fail(node, "unsupported module statement")
        known = set(self.imports) | BUILTINS
        if set(self.classes) & (set(self.imports) | {name for name, _ in self.declarations if "." not in name}):
            self.fail(self.tree, "classes cannot shadow imported or function bindings")
        for name, node in self.declarations:
            if name in self.functions or name in known: self.fail(node, "duplicate or shadowed declaration")
            args = node.args
            if args.posonlyargs or args.kwonlyargs or args.vararg or args.kwarg or args.defaults:
                self.fail(node, "functions require positional parameters without defaults")
            for ann in [node.returns, *(a.annotation for a in args.args)]: self.annotation(ann)
            retry = None
            for decorator in node.decorator_list:
                if not isinstance(node, ast.AsyncFunctionDef): self.fail(decorator, "retry adapter requires an async function")
                if retry is not None: self.fail(decorator, "stacked decorators unsupported")
                retry = self.retry(decorator)
            self.functions[name] = dict(entry=0, parameters=[a.arg for a in args.args],
                locals=[], asynchronous=isinstance(node, ast.AsyncFunctionDef), retry=retry)
        for name, node in self.declarations:
            self.function, self.locals, self.loops = name, list(self.functions[name]["parameters"]), []
            if len(self.locals) != len(set(self.locals)): self.fail(node, "duplicate parameters")
            for child in ast.walk(node):
                if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Store):
                    if child.id not in self.locals: self.locals.append(child.id)
                if isinstance(child, (ast.Global, ast.Nonlocal, ast.Lambda, ast.Yield, ast.YieldFrom)):
                    self.fail(child, "unsupported scope or generator construct")
            self.functions[name].update(entry=len(self.code), locals=self.locals)
            self.block(node.body)
            self.emit(node, "const", self.constant(None))
            self.emit(node, "return")

    def fail(self, node, reason):
        raise UnsupportedPython(f"{self.filename}:{getattr(node, 'lineno', 1)}:{getattr(node, 'col_offset', 0)+1}: {reason}")

    @staticmethod
    def doc(node):
        return isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str)

    def annotation(self, node):
        if node is None: return
        if isinstance(node, (ast.Name, ast.Constant)): return
        if isinstance(node, ast.Attribute): return self.annotation(node.value)
        if isinstance(node, ast.Subscript):
            self.annotation(node.value); self.annotation(node.slice); return
        if isinstance(node, ast.Tuple):
            for item in node.elts: self.annotation(item)
            return
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            self.annotation(node.left); self.annotation(node.right); return
        self.fail(node, "annotation may not execute arbitrary code")

    def dotted(self, node):
        if isinstance(node, ast.Name): return self.imports.get(node.id, node.id)
        if isinstance(node, ast.Attribute): return self.dotted(node.value) + "." + node.attr
        self.fail(node, "expected a declared interface name")

    def retry(self, node):
        if not isinstance(node, ast.Call) or self.dotted(node.func) != "backoff.on_exception":
            self.fail(node, "decorator requires a declared compiler adapter")
        if len(node.args) != 2 or self.dotted(node.args[0]) != "backoff.expo":
            self.fail(node, "supported retry policy is backoff.on_exception(backoff.expo, Exception, max_tries=N)")
        error = self.dotted(node.args[1])
        if self.interfaces.get(error) != "exception": self.fail(node, "retry exception requires an exception interface declaration")
        if len(node.keywords) != 1 or node.keywords[0].arg != "max_tries": self.fail(node, "retry requires literal max_tries only")
        tries = node.keywords[0].value
        if not isinstance(tries, ast.Constant) or type(tries.value) is not int or tries.value < 1:
            self.fail(tries, "max_tries must be a positive integer")
        return dict(exception=error, tries=tries.value, delay="exponential-full-jitter")

    def constant(self, value):
        # Type-tag constants, because True == 1 in Python but their displays differ.
        item = [type(value).__name__, value]
        if item not in self.pool: self.pool.append(item)
        return self.pool.index(item)

    def data(self, value):
        item = ["data", value]
        if item not in self.pool: self.pool.append(item)
        return self.pool.index(item)

    def emit(self, node, op, a=0, b=0):
        index = len(self.code)
        self.code.append([OPS.index(op), a, b])
        self.locations.append([getattr(node, "lineno", 1), getattr(node, "col_offset", 0)+1])
        return index

    def patch(self, index, target): self.code[index][1] = target

    def expr(self, node):
        if isinstance(node, ast.Constant):
            if type(node.value) not in (int, bool, str, type(None)): self.fail(node, "constant outside native value schema")
            self.emit(node, "const", self.constant(node.value))
        elif isinstance(node, ast.Name):
            if node.id in self.locals: self.emit(node, "load", self.locals.index(node.id))
            else:
                name = self.imports.get(node.id, node.id)
                if name not in BUILTINS | {"collections.Counter"} | set(self.functions) | set(self.classes) | set(self.interfaces):
                    self.fail(node, f"name {name!r} has no checked interface")
                self.emit(node, "global", self.constant(name))
        elif isinstance(node, ast.Attribute):
            if node.attr.startswith("__"): self.fail(node, "dunder access is unsupported")
            self.expr(node.value); self.emit(node, "attr", self.constant(node.attr))
        elif isinstance(node, ast.Subscript):
            self.expr(node.value); self.expr(node.slice); self.emit(node, "item")
        elif isinstance(node, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
            if isinstance(node, ast.Dict):
                for key, value in zip(node.keys, node.values):
                    if key is None: self.fail(node, "dictionary unpacking unsupported")
                    self.expr(key); self.expr(value)
                count = len(node.keys)
            else:
                for value in node.elts: self.expr(value)
                count = len(node.elts)
            self.emit(node, "build", self.constant(type(node).__name__.lower()), count)
        elif isinstance(node, ast.BinOp) and type(node.op) in BINARY:
            self.expr(node.left); self.expr(node.right); self.emit(node, "binary", self.constant(BINARY[type(node.op)]))
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.Not, ast.USub, ast.UAdd)):
            self.expr(node.operand); self.emit(node, "unary", self.constant({ast.Not:"not", ast.USub:"neg", ast.UAdd:"pos"}[type(node.op)]))
        elif isinstance(node, ast.Compare):
            # Each chained comparator is evaluated once, and only if needed.
            self.expr(node.left)
            exits = []
            for index, (op, right) in enumerate(zip(node.ops, node.comparators)):
                if type(op) not in BINARY: self.fail(node, "unsupported comparison")
                if isinstance(op, (ast.Is, ast.IsNot)) and not (isinstance(right, ast.Constant) and
                        (right.value is None or type(right.value) is bool)):
                    self.fail(node, "identity comparisons require None/True/False; CPython scalar interning is not modeled")
                self.expr(right)
                if index + 1 < len(node.ops):
                    temp = self.temporary()
                    self.emit(node, "dup"); self.emit(node, "store", temp)
                self.emit(node, "binary", self.constant(BINARY[type(op)]))
                if index + 1 < len(node.ops):
                    self.emit(node, "dup"); exits.append(self.emit(node, "branch"))
                    self.emit(node, "pop"); self.emit(node, "load", temp)
            for jump in exits: self.patch(jump, len(self.code))
        elif isinstance(node, ast.BoolOp):
            exits = []
            for value in node.values[:-1]:
                self.expr(value); self.emit(node, "dup")
                if isinstance(node.op, ast.Or): self.emit(node, "unary", self.constant("not"))
                exits.append(self.emit(node, "branch")); self.emit(node, "pop")
            self.expr(node.values[-1])
            for jump in exits: self.patch(jump, len(self.code))
        elif isinstance(node, ast.IfExp):
            self.expr(node.test); other = self.emit(node, "branch")
            self.expr(node.body); end = self.emit(node, "jump")
            self.patch(other, len(self.code)); self.expr(node.orelse); self.patch(end, len(self.code))
        elif isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id not in self.locals:
                name = self.imports.get(node.func.id, node.func.id)
                arities = {"dict": (0,1), "set": (0,1), "list": (0,1), "tuple": (0,1),
                           "collections.Counter": (0,0), "len": (1,1), "str": (1,1),
                           "repr": (1,1), "bool": (1,1), "int": (1,1), "range": (1,3)}
                if name in arities:
                    low, high = arities[name]
                    if node.keywords or not low <= len(node.args) <= high:
                        self.fail(node, f"{name} call is outside the declared native builtin profile")
                if name in {"max","min","print"} and node.keywords:
                    self.fail(node, f"keyword options for {name} are not modeled")
            self.expr(node.func)
            for arg in node.args: self.expr(arg)
            for kw in node.keywords:
                if kw.arg is None: self.fail(kw, "keyword unpacking unsupported")
                self.expr(kw.value)
            self.emit(node, "call", len(node.args), self.data([kw.arg for kw in node.keywords]))
        elif isinstance(node, ast.Await):
            self.expr(node.value); self.emit(node, "await")
        elif isinstance(node, ast.JoinedStr):
            for part in node.values:
                if isinstance(part, ast.Constant): self.expr(part)
                else:
                    if part.format_spec is not None: self.fail(part, "nonempty format specs unsupported")
                    self.expr(part.value); self.emit(part, "format", part.conversion)
            self.emit(node, "join", len(node.values))
        else: self.fail(node, f"unsupported expression: {type(node).__name__}")

    def temporary(self):
        self.locals.append(f"$temp{len(self.locals)}")
        return len(self.locals)-1

    def assign(self, node):
        if isinstance(node, ast.Name): self.emit(node, "store", self.locals.index(node.id))
        elif isinstance(node, ast.Attribute):
            if node.attr.startswith("__"): self.fail(node, "dunder mutation unsupported")
            self.expr(node.value); self.emit(node, "setattr", self.constant(node.attr))
        elif isinstance(node, ast.Subscript):
            self.expr(node.value); self.expr(node.slice); self.emit(node, "setitem")
        elif isinstance(node, (ast.Tuple, ast.List)):
            self.emit(node, "unpack", len(node.elts))
            for target in node.elts: self.assign(target)
        else: self.fail(node, "unsupported assignment target")

    def block(self, body):
        for node in body:
            if self.doc(node) or isinstance(node, ast.Pass): continue
            if isinstance(node, ast.Expr): self.expr(node.value); self.emit(node, "pop")
            elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                if isinstance(node, ast.AnnAssign): self.annotation(node.annotation)
                if node.value is None: continue
                self.expr(node.value)
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for index, target in enumerate(targets):
                    if index + 1 < len(targets): self.emit(node, "dup")
                    self.assign(target)
            elif isinstance(node, ast.AugAssign):
                if type(node.op) not in BINARY: self.fail(node, "unsupported augmented operation")
                target = node.target
                if isinstance(target, ast.Name): self.expr(target)
                elif isinstance(target, ast.Attribute):
                    self.expr(target.value); self.emit(node, "dup"); self.emit(node, "attr", self.constant(target.attr))
                elif isinstance(target, ast.Subscript):
                    self.expr(target.value); self.expr(target.slice); self.emit(node, "dup2"); self.emit(node, "item")
                else: self.fail(node, "unsupported augmented target")
                self.expr(node.value); self.emit(node, "binary", self.constant("i" + BINARY[type(node.op)]))
                if isinstance(target, ast.Name): self.assign(target)
                elif isinstance(target, ast.Attribute): self.emit(node, "swap"); self.emit(node, "setattr", self.constant(target.attr))
                else:
                    value, key, obj = self.temporary(), self.temporary(), self.temporary()
                    for slot in (value, key, obj): self.emit(node, "store", slot)
                    for slot in (value, obj, key): self.emit(node, "load", slot)
                    self.emit(node, "setitem")
            elif isinstance(node, ast.If):
                self.expr(node.test); other = self.emit(node, "branch")
                self.block(node.body); end = self.emit(node, "jump")
                self.patch(other, len(self.code)); self.block(node.orelse); self.patch(end, len(self.code))
            elif isinstance(node, (ast.While, ast.For)):
                if isinstance(node, ast.For):
                    self.expr(node.iter); self.emit(node, "iter")
                    iterator = self.temporary(); self.emit(node, "store", iterator)
                start = len(self.code)
                if isinstance(node, ast.While): self.expr(node.test); end = self.emit(node, "branch")
                else:
                    self.emit(node, "load", iterator); end = self.emit(node, "next"); self.assign(node.target)
                breaks = []; self.loops.append((start, breaks))
                self.block(node.body); self.emit(node, "jump", start); self.loops.pop()
                self.patch(end, len(self.code)); self.block(node.orelse)
                for jump in breaks: self.patch(jump, len(self.code))
            elif isinstance(node, (ast.Break, ast.Continue)):
                if not self.loops: self.fail(node, "loop control outside loop")
                start, breaks = self.loops[-1]
                if isinstance(node, ast.Continue): self.emit(node, "jump", start)
                else: breaks.append(self.emit(node, "jump"))
            elif isinstance(node, ast.Return):
                if node.value is None: self.emit(node, "const", self.constant(None))
                else: self.expr(node.value)
                self.emit(node, "return")
            elif isinstance(node, ast.Raise):
                if node.exc is None or node.cause is not None: self.fail(node, "raise requires one explicit exception")
                self.expr(node.exc); self.emit(node, "raise")
            elif isinstance(node, ast.Delete):
                for target in node.targets:
                    if not isinstance(target, ast.Subscript): self.fail(target, "only item deletion supported")
                    self.expr(target.value); self.expr(target.slice); self.emit(node, "delitem")
            else: self.fail(node, f"unsupported statement: {type(node).__name__}")

    def artifact(self):
        return dict(instructions=self.code, pool=self.pool, functions=self.functions,
                    classes=self.classes, locations=self.locations, interfaces=self.interfaces)


def parse(path, interfaces=None):
    path = Path(path)
    return Frontend(path.read_text(), path, interfaces).artifact()
