"""Original-coroutine/RM lockstep checks and composed Lean certificates."""
import itertools

import pytest

from zrth.effects import Failed, Finished, Heap, Operation as Op, Pending, Request, Task
from zrth.verified import UnsupportedPython
from zrth.verified_async import compile_coroutine
from .test_verified import load, needs_lean, ROOT


IMPORT = "from zrth.effects import Operation as Op, Request\n"


def compile_text(tmp_path, text, name="step"):
    path = tmp_path / "coroutine.py"
    path.write_text(text)
    return compile_coroutine(path, name)


def compare(bundle, original, *args, heaps=None):
    native, compiled = Task(original(*args)), bundle.task(*args)
    first, second = heaps or (Heap(), Heap())
    out_type = bundle.metadata[bundle.artifact["coroutine"]["stages"][-1]["name"]]["output_type"]
    a, b = native.start(), compiled.start()
    try:
        while isinstance(a, Pending):
            assert isinstance(b, Pending)
            assert a.sequence == b.sequence and a.request == b.request
            assert first.snapshot() == second.snapshot()
            a, b = native.serve(a, first), compiled.serve(b, second)
        assert first.snapshot() == second.snapshot()
        if isinstance(a, Failed):
            assert isinstance(b, Failed)
            assert type(a.error) is type(b.error) and a.error.args == b.error.args
        else:
            assert isinstance(a, Finished) and isinstance(b, Finished)
            assert b.value == out_type.encode(a.value)
        return b
    finally:
        native.close()
        compiled.close()


@needs_lean
def test_direct_async_source_has_real_rm_segments_and_composed_proofs(tmp_path):
    path = ROOT / "examples/compiled_async.py"
    m = load(path, "compiled_async_example")
    b = compile_coroutine(path, "step")
    assert len(b.modules) == 4
    assert all(len(module.atoms) == 1 for module in b.modules.values())
    for key, value in itertools.product((-2**100, 0, 1, 2**100), repeat=2):
        compare(b, m.step, key, value)
    output = b.certify(tmp_path / "checked")
    text = (output / "Certificate.lean").read_text()
    assert "coroutine_frames_valid" in text and "coroutine_execution_correct" in text
    assert "sorryAx" not in (output / "audit.log").read_text()


@needs_lean
def test_locals_helpers_branches_and_fixed_loops_survive_await(tmp_path):
    b = compile_text(tmp_path, IMPORT + '''def plus(x: int, y: int) -> int:
    if x > y:
        return x + y
    return y - x
async def step(x: int, values: tuple[int, int], flag: bool) -> tuple[int, bool, int]:
    total = x
    for value in values:
        total = plus(total, value)
    if flag:
        total = total + 10
    else:
        total = total - 10
    reference = await Request(Op.NEW_DICT)
    await Request(Op.DICT_SET, reference, key=plus(x, total), value=total)
    total = await Request(Op.DICT_ITEM, reference, plus(x, total))
    return (total, flag, x)
''')
    m = load(tmp_path / "coroutine.py", "async_live_locals")
    for x, flag in itertools.product((-5, 0, 9), (True, False)):
        compare(b, m.step, x, (-7, 12), flag)
    b.certify(tmp_path / "checked")


@needs_lean
def test_typed_records_remain_in_frames(tmp_path):
    b = compile_text(tmp_path, IMPORT + '''from dataclasses import dataclass
@dataclass(frozen=True)
class Item:
    value: int
    flag: bool
async def step(item: Item) -> Item:
    reference = await Request(Op.NEW_SET)
    await Request(Op.SET_ADD, reference, item.value)
    size = await Request(Op.SET_LEN, reference)
    return Item(item.value + size, item.flag)
''')
    m = load(tmp_path / "coroutine.py", "async_records")
    for value, flag in itertools.product((-8, 3), (True, False)):
        compare(b, m.step, m.Item(value, flag))
    b.certify(tmp_path / "checked")


@needs_lean
def test_set_aliases_copy_and_return_await(tmp_path):
    b = compile_text(tmp_path, IMPORT + '''async def step(key: int) -> int:
    reference = await Request(Op.NEW_SET)
    alias = reference
    await Request(Op.SET_ADD, alias, key)
    copied = await Request(Op.SET_COPY, reference)
    await Request(Op.SET_REMOVE, reference, key)
    return await Request(Op.SET_CONTAINS, copied, key)
''')
    m = load(tmp_path / "coroutine.py", "async_set_aliases")
    for key in (-2**100, 0, 7):
        compare(b, m.step, key)
    assert b.run(7) == [1]
    b.certify(tmp_path / "checked")


@needs_lean
def test_errors_stop_before_later_requests(tmp_path):
    b = compile_text(tmp_path, IMPORT + '''async def step(key: int) -> int:
    reference = await Request(Op.NEW_DICT)
    result = await Request(Op.DICT_ITEM, reference, key)
    await Request(Op.NEW_SET)
    return result
''')
    m = load(tmp_path / "coroutine.py", "async_missing_key")
    result = compare(b, m.step, 99)
    assert isinstance(result, Failed) and isinstance(result.error, KeyError)
    b.certify(tmp_path / "checked")


@needs_lean
def test_async_without_await(tmp_path):
    b = compile_text(tmp_path, "async def step(x: int) -> int:\n    return x + 1\n")
    assert b.run(4) == [5]
    b.certify(tmp_path / "checked")


def test_compiled_tasks_interleave_and_reject_replayed_tokens(tmp_path):
    b = compile_text(tmp_path, IMPORT + '''async def step(reference: int, key: int) -> int:
    await Request(Op.SET_ADD, reference, key)
    return await Request(Op.SET_LEN, reference)
''')
    heap = Heap()
    reference = heap.apply(Request(Op.NEW_SET)).unwrap()
    a, c = b.task(reference, 7), b.task(reference, 7)
    first, other = a.start(), c.start()
    second, last = a.serve(first, heap), c.serve(other, heap)
    before = heap.snapshot()
    for bad in (first, last):
        with pytest.raises(RuntimeError): a.serve(bad, heap)
        assert heap.snapshot() == before
    assert a.serve(second, heap) == c.serve(last, heap) == Finished([1])


@pytest.mark.parametrize("text", [
    "async def step(x: int) -> int:\n    if x > 0:\n        x = await Request(Op.NEW_DICT)\n    return x\n",
    "async def step(x: int) -> int:\n    for i in (1, 2):\n        await Request(Op.NEW_DICT)\n    return x\n",
    "async def step(x: int) -> int:\n    return 1 + await Request(Op.NEW_DICT)\n",
    "async def step(x: int) -> int:\n    if x > 0:\n        return x\n    return 0\n",
    "async def helper() -> int:\n    return 1\nasync def step(x: int) -> int:\n    y = await helper()\n    return y\n",
    "async def step(x: int) -> int:\n    y = await Request(x)\n    return y\n",
    "async def step(x: int) -> int:\n    y = await Request(Op.NOT_AN_OPERATION)\n    return y\n",
    "async def step(x: int) -> int:\n    y = await Request(Op.NEW_DICT, True)\n    return y\n",
    "async def step(x: int) -> int:\n    y = await Request(Op.NEW_DICT, reference=x, unknown=x)\n    return y\n",
    "async def step(x: int) -> int:\n    y = await Request(Op.NEW_DICT, x, reference=x)\n    return y\n",
    "async def step(x: int) -> int:\n    Op = x\n    return x\n",
    "async def step(Request: int) -> int:\n    return Request\n",
    "async def step(x: int) -> int:\n    a, b = await Request(Op.NEW_DICT)\n    return a\n",
    "async def step(x: int) -> int:\n    y: bool = await Request(Op.NEW_DICT)\n    return x\n",
    "async def step(x: int) -> int:\n    print(x)\n    return x\n",
    "async def step(x: int) -> int:\n    try:\n        y = await Request(Op.NEW_DICT)\n    except Exception:\n        pass\n    return x\n",
    "async def step(x: int = dangerous()) -> int:\n    return x\n",
    "async def step(x: int) -> int:\n    return x\nasync def unused(x: dangerous()) -> int:\n    return 0\n",
])
def test_fail_closed_with_locations(tmp_path, text):
    with pytest.raises(UnsupportedPython, match=r"coroutine.py:\d+:\d+:"):
        compile_text(tmp_path, IMPORT + text)


def test_partial_frame_initialization_is_rejected(tmp_path):
    with pytest.raises(ValueError):
        compile_text(tmp_path, IMPORT + '''async def step(flag: bool) -> int:
    if flag:
        x = 1
    reference = await Request(Op.NEW_DICT)
    return reference
''')


@needs_lean
def test_tampered_rm_segment_is_rejected(tmp_path):
    b = compile_text(tmp_path, IMPORT + '''async def step(x: int) -> int:
    reference = await Request(Op.NEW_DICT)
    return x + 1
''')
    graph = b.artifact["functions"]["step_stage_1"]["graph"]
    for term in graph["terms"]:
        if term == ["lit", 1]: term[1] = 2
    with pytest.raises(ValueError, match="Lean rejected"):
        b.certify(tmp_path / "bad")


def test_tampered_effect_or_stage_order_is_rejected(tmp_path):
    b = compile_text(tmp_path, IMPORT + '''async def step(x: int) -> int:
    reference = await Request(Op.NEW_DICT)
    return x
''')
    b.artifact["coroutine"]["stages"][0]["effect"] = "NEW_SET"
    with pytest.raises(ValueError, match="boundaries differ"):
        b.write(tmp_path / "bad")


def test_stale_source_is_rejected(tmp_path):
    b = compile_text(tmp_path, "async def step(x: int) -> int:\n    return x\n")
    (tmp_path / "coroutine.py").write_text("async def step(x: int) -> int:\n    return x + 1\n")
    with pytest.raises(ValueError, match="source changed"):
        b.write(tmp_path / "stale")


@pytest.mark.parametrize("operation", list(Op))
def test_every_heap_operation_is_forwarded_exactly(tmp_path, operation):
    b = compile_text(tmp_path, IMPORT + f'''async def step(reference: int, key: int, value: int) -> int:
    return await Request(Op.{operation.name}, reference, key, value)
''')
    m = load(tmp_path / "coroutine.py", "async_operation_" + operation.name)
    for reference in (0, 1, -1):
        heaps = Heap(), Heap()
        for heap in heaps:
            heap.apply(Request(Op.NEW_DICT))
            heap.apply(Request(Op.NEW_SET))
            heap.apply(Request(Op.DICT_SET, 0, 5, 91))
            heap.apply(Request(Op.SET_ADD, 1, 5))
        compare(b, m.step, reference, 5, -19, heaps=heaps)


def test_alias_imports_and_zero_argument_entrypoint(tmp_path):
    b = compile_text(tmp_path, '''from zrth.effects import Operation as Action, Request as Effect
async def step() -> int:
    return await Effect(Action.NEW_DICT)
''')
    assert b.run() == [0]


def test_importing_the_compiler_never_executes_source(tmp_path):
    source = IMPORT + '''async def step(x: int) -> int:
    return x
print("must not execute")
'''
    with pytest.raises(UnsupportedPython, match="unsupported module statement"):
        compile_text(tmp_path, source)


def test_frame_schema_cannot_be_changed_after_compilation(tmp_path):
    b = compile_text(tmp_path, IMPORT + '''async def step(x: int) -> int:
    reference = await Request(Op.NEW_DICT)
    return x
''')
    b.artifact["functions"]["step_stage_1"]["parameters"][0][1]["name"] = "bool"
    with pytest.raises(ValueError, match="source AST/schema differs"):
        b.write(tmp_path / "bad")
