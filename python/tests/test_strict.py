"""Algorithm-independent strict frontend regressions; execute actual RM terms."""
import ast
import inspect
import torch
import pytest

from zrth import Var, Int, Bool, X, LIATermBuilder
from zrth.analyzer import convert_method
from zrth.eval import eval_itype
from zrth.strict import ScalarValidator, StrictPythonError


def evaluate(terms, initial):
    values = dict(initial)
    for term in terms:
        output = eval_itype(term.itype, [values[w] for w in term.read], term.write[0].dtype)
        values.update(zip(term.write, output))
    return values


class Sequential:
    def step(self, delta):
        self.x = self.x + delta
        local: int = self.x + 2
        if self.x > 5:
            self.y = local
        else:
            self.y = self.y


@pytest.mark.parametrize("x,delta,y", [(0, 1, 8), (4, 3, 2), (8, -4, 6)])
def test_sequential_assignments_and_annotations(x, delta, y):
    wires = {name: Var(Int([1, 1])) for name in ("x", "y", "delta")}
    terms = convert_method(Sequential.step, wires, [], builder=LIATermBuilder(), strict=True)
    result = evaluate(terms, {wires[k]: torch.tensor([[v]]) for k, v in dict(x=x, y=y, delta=delta).items()})
    original = Sequential()
    original.x, original.y = x, y
    original.step(delta)
    assert result[X(wires["x"])].item() == original.x
    assert result[X(wires["y"])].item() == original.y


class Boolean:
    def step(self, enabled):
        if enabled and not self.flag:
            self.flag = True
        else:
            self.flag = False


@pytest.mark.parametrize("enabled,flag", [(False, False), (False, True), (True, False), (True, True)])
def test_boolean_branches(enabled, flag):
    wires = {name: Var(Bool([1, 1])) for name in ("enabled", "flag")}
    terms = convert_method(Boolean.step, wires, [], builder=LIATermBuilder(), strict=True)
    result = evaluate(terms, {wires["enabled"]: torch.tensor([[enabled]]), wires["flag"]: torch.tensor([[flag]])})
    assert result[X(wires["flag"])].item() == (enabled and not flag)


@pytest.mark.parametrize("body", [
    "print(self.x)", "self.items.add(value)", "self.items[value] = 1",
    "for i in range(3):\n        self.x += 1", "while value:\n        self.x += 1",
    "self.x = unknown(value)", "self.x = self.helper(value)",
    "self.x = max(value, default=0)", "self.x = [value]", "self.x = {value: 1}",
    "self.x = [i for i in range(3)]", "del self.x", "raise ValueError()",
    "assert value > 0", "with context():\n        self.x += 1",
    "try:\n        self.x += 1\n    except Exception:\n        pass",
    "self.unknown = value", "value.x = 1", "self.x = lambda: value",
    "x = y = value", "self.x = (value, value)", "_ret_0 = value",
    "min = value", "self = value", "def nested():\n        return value",
    "self.x = (value := 2)",
])
def test_unsupported_syntax_is_source_located(body):
    tree = ast.parse("def step(self, value):\n    " + body)
    with pytest.raises(StrictPythonError, match=r"example.py:\d+:\d+:"):
        ScalarValidator({"x": None, "items": None, "value": None}, "example.py", 10).visit(tree.body[0])


def test_async_is_rejected_not_traversed_as_synchronous():
    tree = ast.parse("async def step(self):\n    await send()")
    with pytest.raises(StrictPythonError, match="AsyncFunctionDef"):
        ScalarValidator({}, "example.py", 1).visit(tree.body[0])


class NumericCondition:
    def step(self, value):
        if value:
            self.x = 1
        else:
            self.x = 0


def test_numeric_truthiness_is_not_silently_booleanized():
    wires = {name: Var(Int([1, 1])) for name in ("x", "value")}
    with pytest.raises(StrictPythonError, match="Boolean conditions") as caught:
        convert_method(NumericCondition.step, wires, [], builder=LIATermBuilder(), strict=True)
    assert caught.value.filename == __file__
    assert caught.value.lineno >= inspect.getsourcelines(NumericCondition.step)[1]


def test_tensor_conditions_are_not_python_scalar_conditions():
    wires = {name: Var(Bool([2, 2])) for name in ("enabled", "flag")}
    with pytest.raises(StrictPythonError, match="wire shapes"):
        convert_method(Boolean.step, wires, [], builder=LIATermBuilder(), strict=True)
