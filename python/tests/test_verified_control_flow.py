"""Checked helper scopes, fixed-tuple iteration, and Python differential checks."""
import itertools
import json

import pytest

from zrth.verified import UnsupportedPython, compile_module
from .test_verified import compile_text, load, matches, needs_lean, ROOT


def test_fold_register_matches_python():
    path = ROOT / "examples/fold_register.py"
    m = load(path, "fold_register_example")
    b = compile_module(path, ["step", "higher"])
    for state, a, c, d in itertools.product((-2**100, -1, 0, 2**100), repeat=4):
        matches(b, "step", m.step, m.State(state), (a, c, d))
        matches(b, "higher", m.higher, state, a)


@pytest.mark.parametrize("size", [1, 2, 5, 8])
def test_loop_layout_is_not_hardcoded_to_three(tmp_path, size):
    schema = ", ".join(["int"] * size)
    b = compile_text(tmp_path, f'''def step(values: tuple[{schema}]) -> int:
    total = 0
    for value in values:
        total = total + value
    return total
''')
    values = tuple(range(-size, 0))
    assert b.run("step", values) == [sum(values)]


@needs_lean
def test_helpers_and_loops_over_mixed_sort_records(tmp_path):
    b = compile_text(tmp_path, '''from dataclasses import dataclass
@dataclass(frozen=True)
class Item:
    value: int
    flag: bool
def flip(item: Item) -> Item:
    return Item(item.value + 1, not item.flag)
def step(items: tuple[Item, Item]) -> tuple[int, bool]:
    total = 0
    parity = False
    for item in items:
        changed = flip(item)
        total = total + changed.value
        parity = parity != changed.flag
    return (total, parity)
''')
    m = load(tmp_path / "source.py", "record_helpers")
    for x, y, a, c in itertools.product((-3, 7), (-5, 0), (True, False), (True, False)):
        matches(b, "step", m.step, (m.Item(x, a), m.Item(y, c)))
    b.certify(tmp_path / "checked")


@needs_lean
def test_helper_scopes_nested_calls_keywords_and_early_return(tmp_path):
    b = compile_text(tmp_path, '''def adjust(x: int, y: int) -> int:
    if x > y:
        return x + 1
    x = y - 1
    return x
def combine(x: int, y: int) -> int:
    return adjust(y=adjust(x, y), x=y)
def step(x: int, y: int) -> tuple[int, int, int]:
    result = combine(x, y)
    return (x, y, result)
''')
    m = load(tmp_path / "source.py", "helper_scopes")
    for x, y in itertools.product((-2**100, -1, 0, 5, 2**100), repeat=2):
        matches(b, "step", m.step, x, y)
    assert '"call"' in json.dumps(b.artifact["functions"]["step"]["source"])
    b.certify(tmp_path / "checked")


@needs_lean
def test_lazy_calls_and_optional_record_refinement(tmp_path):
    b = compile_text(tmp_path, '''from dataclasses import dataclass
@dataclass(frozen=True)
class Box:
    value: int
def positive(x: int) -> bool:
    return x > 0
def identity(x: int) -> int:
    return x
def step(box: Box | None) -> tuple[bool, bool, int]:
    a = box is not None and positive(box.value)
    b = box is None or positive(box.value)
    c = identity(box.value) if box is not None else identity(-1)
    return (a, b, c)
''')
    m = load(tmp_path / "source.py", "lazy_helpers")
    for value in (None, m.Box(-2), m.Box(0), m.Box(99)):
        matches(b, "step", m.step, value)
    b.certify(tmp_path / "checked")


@needs_lean
def test_tuple_unpacking_aliases_indices_and_len(tmp_path):
    b = compile_text(tmp_path, '''def pair(x: int, y: int) -> tuple[int, int]:
    return (y, x)
def step(x: int, y: int) -> tuple[int, int, int, int]:
    x, y = pair(x, y)
    x, x = (x, y)
    a, (b, c) = (x, (y, x + y))
    values = (a, b, c)
    return (x, values[-1], values[0], len(values))
''')
    m = load(tmp_path / "source.py", "unpacking_helpers")
    for x, y in itertools.product((-7, 0, 3, 2**100), repeat=2):
        matches(b, "step", m.step, x, y)
    b.certify(tmp_path / "checked")


@needs_lean
def test_loop_snapshot_loop_variable_and_else(tmp_path):
    b = compile_text(tmp_path, '''def plus(a: int, b: int) -> int:
    return a + b
def step(values: tuple[int, int, int], early: bool) -> tuple[int, int, int]:
    total = 0
    for value in values:
        total = plus(total, value)
        values = (99, 98, 97)
        if early and value > 0:
            return (total, value, values[0])
    else:
        total = total + 10
    return (total, value, values[0])
''')
    m = load(tmp_path / "source.py", "loop_snapshot")
    for values in itertools.product((-3, 0, 4), repeat=3):
        for early in (True, False):
            matches(b, "step", m.step, values, early)
    assert '"forEach"' in json.dumps(b.artifact["functions"]["step"]["source"])
    b.certify(tmp_path / "checked")


@needs_lean
def test_nested_loops_and_destructured_loop_targets(tmp_path):
    b = compile_text(tmp_path, '''def step(values: tuple[tuple[int, int], tuple[int, int]]) -> int:
    total = 0
    for a, b in values:
        for x in (a, b):
            total = total + x
    return total
''')
    m = load(tmp_path / "source.py", "nested_loops")
    for a, second, c, d in itertools.product((-4, 3), repeat=4):
        matches(b, "step", m.step, ((a, second), (c, d)))
    b.certify(tmp_path / "checked")


@needs_lean
def test_loop_inside_helper_does_not_return_from_caller(tmp_path):
    b = compile_text(tmp_path, '''def first_positive(values: tuple[int, int]) -> int:
    for value in values:
        if value > 0:
            return value
    return -1
def step(values: tuple[int, int]) -> int:
    return first_positive(values) + 100
''')
    m = load(tmp_path / "source.py", "helper_loop")
    for values in itertools.product((-9, 0, 4), repeat=2):
        matches(b, "step", m.step, values)
    b.certify(tmp_path / "checked")


@needs_lean
def test_nonempty_loop_initializes_locals(tmp_path):
    b = compile_text(tmp_path, '''def step(values: tuple[int, int]) -> int:
    for value in values:
        result = value
    return result
''')
    assert b.run("step", (3, 8)) == [8]
    b.certify(tmp_path / "checked")


@pytest.mark.parametrize("text", [
    "def step(x: int) -> int:\n    return step(x)\n",
    "def first(x: int) -> int:\n    return step(x)\ndef step(x: int) -> int:\n    return first(x)\n",
    "def helper(x: int) -> int:\n    return x\ndef step(x: int) -> int:\n    helper = x\n    return helper\n",
    "def helper(x: int) -> int:\n    return x\ndef step(x: int) -> int:\n    return helper()\n",
    "def helper(x: int) -> int:\n    return x\ndef step(x: int) -> int:\n    return helper(x, x)\n",
    "def helper(x: int) -> int:\n    return x\ndef step(x: int) -> int:\n    return helper(x, x=x)\n",
    "def helper(x: int) -> int:\n    return x\ndef step(x: int) -> int:\n    return helper(unknown=x)\n",
    "def helper(x: int) -> int:\n    return x\ndef step(x: int) -> int:\n    return helper(*((x, x)))\n",
    "def helper(x: int) -> int:\n    return x\ndef step(x: int) -> int:\n    return helper(True)\n",
    "def step(x: int) -> int:\n    return (x, x)[x]\n",
    "def step(x: int) -> int:\n    return (x, x)[2]\n",
    "def step(x: int) -> int:\n    return (x, x)[-3]\n",
    "def step(x: int) -> int:\n    return (x, x)[True]\n",
    "def step(x: int) -> int:\n    a, b = (x, x, x)\n    return a\n",
    "def step(x: int) -> int:\n    a, *b = (x, x)\n    return a\n",
    "def step(x: int) -> int:\n    len = x\n    return len\n",
    "def step(x: int) -> int:\n    for value in (x, True):\n        pass\n    return x\n",
    "def step(x: int) -> int:\n    for value in range(x):\n        pass\n    return x\n",
    "def step(x: int) -> int:\n    for value in (x, x):\n        break\n    return x\n",
    "def step(x: int) -> int:\n    for value in (x, x):\n        continue\n    return x\n",
    "def step(x: int) -> int:\n    return len(())\n",
])
def test_unsupported_control_flow_has_locations(tmp_path, text):
    with pytest.raises(UnsupportedPython, match=r"source.py:\d+:\d+:"):
        compile_text(tmp_path, text)


def test_helper_must_return_and_cannot_capture_caller_locals(tmp_path):
    with pytest.raises(ValueError, match="every helper path must return"):
        compile_text(tmp_path, '''def helper(x: int) -> int:
    if x > 0:
        return x
def step(x: int) -> int:
    return helper(x)
''')
    with pytest.raises(UnsupportedPython):
        compile_text(tmp_path, '''def helper(x: int) -> int:
    return private
def step(x: int) -> int:
    private = x
    return helper(x)
''')


def test_tuple_input_shape_is_checked(tmp_path):
    b = compile_text(tmp_path, "def step(xs: tuple[int, int]) -> int:\n    return len(xs)\n")
    for bad in ((1,), (1, 2, 3), [1, 2]):
        with pytest.raises(TypeError, match="exact tuple"):
            b.run("step", bad)


@needs_lean
def test_certificate_rejects_wrong_loop_result(tmp_path):
    b = compile_text(tmp_path, '''def step(values: tuple[int, int]) -> int:
    total = 0
    for value in values:
        total = total + value
    return total
''')
    graph = b.artifact["functions"]["step"]["graph"]
    for term in graph["terms"]:
        if term[:2] == ["bin", "add"]:
            term[1] = "sub"
            break
    with pytest.raises(ValueError, match="Lean rejected"):
        b.certify(tmp_path / "bad")


def test_loop_cannot_reuse_stale_optional_refinement(tmp_path):
    with pytest.raises(UnsupportedPython, match="explicit is-not-None"):
        compile_text(tmp_path, '''from dataclasses import dataclass
@dataclass(frozen=True)
class Box:
    value: int
def step(box: Box | None) -> int:
    total = 0
    if box is not None:
        for x in (1, 2):
            total = total + box.value
            box = None
    return total
''')


@needs_lean
def test_len_cannot_hide_read_of_uninitialized_local(tmp_path):
    b = compile_text(tmp_path, '''def step(flag: bool) -> int:
    if flag:
        values = (1, 2)
    return len(values)
''')
    with pytest.raises(ValueError, match="Lean rejected"):
        b.certify(tmp_path / "uninitialized")


@needs_lean
def test_helper_argument_is_checked_even_when_unused(tmp_path):
    b = compile_text(tmp_path, '''def helper(x: int) -> int:
    return 5
def step(flag: bool) -> int:
    if flag:
        value = 1
    return helper(value)
''')
    with pytest.raises(ValueError, match="Lean rejected"):
        b.certify(tmp_path / "uninitialized")


@needs_lean
def test_optional_widening_in_unpacking_and_loop_targets(tmp_path):
    b = compile_text(tmp_path, '''def step(values: tuple[int, int]) -> tuple[int | None, int]:
    optional: int | None = None
    optional, other = values
    for optional in values:
        pass
    return (optional, other)
''')
    m = load(tmp_path / "source.py", "optional_target_widening")
    matches(b, "step", m.step, (3, 9))
    b.certify(tmp_path / "checked")


@needs_lean
def test_boolean_equality_uses_boolean_rm_operators(tmp_path):
    b = compile_text(tmp_path, '''def step(a: bool, b: bool) -> tuple[bool, bool]:
    return (a == b, a != b)
''')
    m = load(tmp_path / "source.py", "boolean_equality")
    for a, c in itertools.product((True, False), repeat=2):
        matches(b, "step", m.step, a, c)
    b.certify(tmp_path / "checked")
