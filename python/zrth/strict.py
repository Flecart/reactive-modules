"""Fail-closed validation for the scalar Python-to-RM frontend.

This is an opt-in supported-language check, not a compiler-correctness proof.
Keep the legacy permissive frontend available for delegated gym environments.
"""
import ast

from .analyzer import UnsupportedFeatureError


class StrictPythonError(UnsupportedFeatureError):
    """A source-located rejection of unsupported Python behavior."""

    def __init__(self, message, node, filename, first_line):
        self.filename = filename
        self.lineno = first_line + getattr(node, "lineno", 1) - 1
        self.column = getattr(node, "col_offset", 0) + 1
        super().__init__(f"{filename}:{self.lineno}:{self.column}: {message}")


class ScalarValidator(ast.NodeVisitor):
    """Validate the deliberately small, side-effect-free expression language."""

    allowed = (
        ast.FunctionDef, ast.arguments, ast.arg, ast.Assign, ast.AnnAssign,
        ast.AugAssign, ast.If, ast.Return, ast.Pass, ast.Expr,
        ast.Name, ast.Attribute, ast.Constant, ast.BinOp, ast.UnaryOp,
        ast.BoolOp, ast.Compare, ast.IfExp, ast.Call, ast.Tuple,
        ast.Load, ast.Store, ast.Add, ast.Sub, ast.Mult, ast.USub, ast.UAdd,
        ast.Not, ast.And, ast.Or, ast.Eq, ast.NotEq, ast.Lt, ast.LtE,
        ast.Gt, ast.GtE,
    )

    def __init__(self, wires, filename, first_line):
        self.wires = wires
        self.filename = filename
        self.first_line = first_line
        self.in_function = False

    def reject(self, node, message):
        raise StrictPythonError(message, node, self.filename, self.first_line)

    def generic_visit(self, node):
        if not isinstance(node, self.allowed):
            self.reject(node, f"{type(node).__name__} is not supported in strict scalar mode")
        super().generic_visit(node)

    def visit_FunctionDef(self, node):
        if self.in_function:
            self.reject(node, "nested functions are not supported")
        self.in_function = True
        if node.decorator_list:
            self.reject(node.decorator_list[0], "decorators require an explicit semantics")
        args = node.args
        if args.vararg or args.kwarg or args.posonlyargs or args.kwonlyargs:
            self.reject(node, "only ordinary positional parameters are supported")
        parameters = {a.arg for a in args.args if a.arg != "self"}
        if parameters & {"min", "max"}:
            self.reject(node, "min/max builtin names must not be shadowed")
        missing = parameters - self.wires.keys()
        if missing:
            self.reject(node, f"parameters need declared input wires: {sorted(missing)}")
        fields = {n.attr for n in ast.walk(node) if isinstance(n, ast.Attribute)
                  and isinstance(n.value, ast.Name) and n.value.id == "self"}
        if fields & parameters:
            self.reject(node, "parameter names must not shadow self fields")
        for statement in node.body:
            self.visit(statement)

    def visit_Name(self, node):
        if node.id.startswith("_ret_"):
            self.reject(node, "_ret_ names are reserved by return normalization")
        if isinstance(node.ctx, ast.Store) and node.id in ("self", "min", "max"):
            self.reject(node, f"assignment to reserved name {node.id!r}")

    def visit_Attribute(self, node):
        if not isinstance(node.value, ast.Name) or node.value.id != "self":
            self.reject(node, "only declared self fields are supported")
        if node.attr not in self.wires:
            self.reject(node, f"undeclared state field: self.{node.attr}")

    def visit_Assign(self, node):
        if len(node.targets) != 1:
            self.reject(node, "chained assignments are not supported")
        if not isinstance(node.targets[0], (ast.Name, ast.Attribute)):
            self.reject(node.targets[0], "assignment requires a name or declared self field")
        self.generic_visit(node)

    def visit_AnnAssign(self, node):
        if node.value is None:
            self.reject(node, "annotation-only statements are not supported")
        if not isinstance(node.target, (ast.Name, ast.Attribute)):
            self.reject(node.target, "assignment requires a name or declared self field")
        self.visit(node.target)
        self.visit(node.value)

    def visit_AugAssign(self, node):
        if not isinstance(node.target, (ast.Name, ast.Attribute)):
            self.reject(node.target, "augmented assignment requires a name or self field")
        self.generic_visit(node)

    def visit_Expr(self, node):
        if not isinstance(node.value, ast.Constant) or not isinstance(node.value.value, str):
            self.reject(node, "expression statements may have effects; only docstrings are supported")

    def visit_Constant(self, node):
        if type(node.value) not in (bool, int, float):
            self.reject(node, "only numeric and Boolean expression constants are supported")

    def visit_Call(self, node):
        if not isinstance(node.func, ast.Name) or node.func.id not in ("min", "max"):
            self.reject(node, "only min/max calls are supported; other calls need explicit semantics")
        if len(node.args) != 2 or node.keywords:
            self.reject(node, "min/max require exactly two positional arguments")
        for arg in node.args:
            self.visit(arg)

    def visit_Tuple(self, node):
        self.reject(node, "tuples are supported only as multiple return values")

    def visit_Return(self, node):
        if node.value is not None:
            for value in node.value.elts if isinstance(node.value, ast.Tuple) else [node.value]:
                self.visit(value)
