"""Executable integer-container and explicit-coroutine boundary regressions."""
import random

import pytest

from zrth.effects import (Failed, Finished, Heap, InvalidReference, Operation as Op,
                          Pending, Request, Response, Task, WrongKind, run)


def call(heap, op, ref=0, key=0, value=0):
    return heap.apply(Request(op, ref, key, value)).unwrap()


def test_dictionary_order_aliasing_deletion_and_copy():
    heap = Heap()
    ref = call(heap, Op.NEW_DICT)
    alias = ref
    for key, value in [(5, 0), (-7, 4), (5, 9)]:
        call(heap, Op.DICT_SET, ref, key, value)
    assert call(heap, Op.DICT_ITEM, alias, 5) == 9
    assert call(heap, Op.DICT_KEY_AT, ref, 0) == 5
    assert call(heap, Op.DICT_KEY_AT, ref, -1) == -7
    copy = call(heap, Op.DICT_COPY, ref)
    call(heap, Op.DICT_DELETE, alias, 5)
    call(heap, Op.DICT_SET, alias, 5, 20)
    assert call(heap, Op.DICT_KEY_AT, ref, -1) == 5
    assert call(heap, Op.DICT_ITEM, copy, 5) == 9
    call(heap, Op.DICT_CLEAR, copy)
    assert call(heap, Op.DICT_LEN, copy) == 0
    assert call(heap, Op.DICT_LEN, ref) == 2


def test_absence_is_not_zero_or_empty():
    heap = Heap()
    ref = call(heap, Op.NEW_DICT)
    call(heap, Op.DICT_SET, ref, 9, 0)
    assert call(heap, Op.DICT_CONTAINS, ref, 9) == 1
    assert call(heap, Op.DICT_CONTAINS, ref, 10) == 0
    assert call(heap, Op.DICT_GET, ref, 10, -999) == -999
    assert call(heap, Op.DICT_ITEM, ref, 9) == 0
    with pytest.raises(KeyError):
        call(heap, Op.DICT_ITEM, ref, 10)


def test_sets_deduplicate_discard_remove_and_copy():
    heap = Heap()
    ref = call(heap, Op.NEW_SET)
    call(heap, Op.SET_ADD, ref, 2)
    call(heap, Op.SET_ADD, ref, 2)
    assert call(heap, Op.SET_LEN, ref) == 1
    copied = call(heap, Op.SET_COPY, ref)
    call(heap, Op.SET_DISCARD, ref, 77)
    call(heap, Op.SET_REMOVE, ref, 2)
    assert call(heap, Op.SET_CONTAINS, copied, 2) == 1
    assert call(heap, Op.SET_LEN, ref) == 0
    with pytest.raises(KeyError):
        call(heap, Op.SET_REMOVE, ref, 2)
    call(heap, Op.SET_CLEAR, copied)
    assert call(heap, Op.SET_LEN, copied) == 0


@pytest.mark.parametrize("effect,error", [
    (Request(Op.DICT_ITEM, -1), InvalidReference),
    (Request(Op.DICT_ITEM, 2**100), InvalidReference),
    (Request(Op.DICT_ITEM, 1), WrongKind),
    (Request(Op.SET_ADD, 0), WrongKind),
    (Request(Op.DICT_DELETE, 0, 3), KeyError),
    (Request(Op.DICT_ITEM, 0, 3), KeyError),
    (Request(Op.SET_REMOVE, 1, 3), KeyError),
    (Request(Op.DICT_KEY_AT, 0, -1), IndexError),
    (Request(Op.DICT_KEY_AT, 0, 2**100), IndexError),
])
def test_errors_preserve_heap(effect, error):
    heap = Heap()
    call(heap, Op.NEW_DICT)
    call(heap, Op.NEW_SET)
    before = heap.snapshot()
    result = heap.apply(effect)
    with pytest.raises(error):
        result.unwrap()
    assert heap.snapshot() == before


def test_no_small_container_or_integer_bound():
    heap = Heap()
    dictionary, seen = call(heap, Op.NEW_DICT), call(heap, Op.NEW_SET)
    for i in range(1200):
        call(heap, Op.DICT_SET, dictionary, 2**150 + i, -(2**180) - i)
        call(heap, Op.SET_ADD, seen, 2**150 + i)
    assert call(heap, Op.DICT_LEN, dictionary) == call(heap, Op.SET_LEN, seen) == 1200
    assert call(heap, Op.DICT_ITEM, dictionary, 2**150 + 1199) == -(2**180) - 1199


@pytest.mark.parametrize("bad", [True, False, 1.0, "1", None])
def test_exact_integer_schema_rejects_unsupported_keys(bad):
    with pytest.raises(TypeError):
        Request(Op.DICT_SET, 0, bad, 1)


@pytest.mark.parametrize("seed", range(8))
def test_against_native_python_containers(seed):
    rng = random.Random(seed)
    heap = Heap()
    dictionary, seen = {}, set()
    d, s = call(heap, Op.NEW_DICT), call(heap, Op.NEW_SET)
    for _ in range(250):
        key, value = rng.randrange(-9, 10), rng.randrange(-100, 100)
        op = rng.randrange(6)
        if op == 0:
            dictionary[key] = value
            call(heap, Op.DICT_SET, d, key, value)
        elif op == 1:
            assert call(heap, Op.DICT_GET, d, key, value) == dictionary.get(key, value)
        elif op == 2:
            assert call(heap, Op.DICT_CONTAINS, d, key) == int(key in dictionary)
        elif op == 3:
            seen.add(key)
            call(heap, Op.SET_ADD, s, key)
        elif op == 4:
            seen.discard(key)
            call(heap, Op.SET_DISCARD, s, key)
        else:
            assert call(heap, Op.SET_CONTAINS, s, key) == int(key in seen)
        assert heap.snapshot() == (("dict", tuple(dictionary.items())), ("set", frozenset(seen)))


async def example(key, value):
    ref = await Request(Op.NEW_DICT)
    await Request(Op.DICT_SET, ref, key, value)
    return await Request(Op.DICT_ITEM, ref, key)


def test_coroutine_really_suspends_before_each_effect():
    heap = Heap()
    task = Task(example(8, 99))
    first = task.start()
    assert first.sequence == 0 and first.request.operation == Op.NEW_DICT
    assert heap.snapshot() == ()
    second = task.serve(first, heap)
    assert second.sequence == 1 and heap.snapshot() == (("dict", ()),)
    third = task.serve(second, heap)
    assert third.sequence == 2 and heap.snapshot() == (("dict", ((8, 99),)),)
    final = task.serve(third, heap)
    assert final == Finished(99)


def test_replayed_or_forged_tokens_do_not_execute_effect_twice():
    heap = Heap()
    task = Task(example(2, 3))
    first = task.start()
    second = task.serve(first, heap)
    snapshot = heap.snapshot()
    for invalid in (first, Pending(second.sequence, second.request), None):
        with pytest.raises(RuntimeError, match="suspension token"):
            task.serve(invalid, heap)
        assert heap.snapshot() == snapshot
    task.close()


def test_foreign_task_token_is_rejected():
    heap = Heap()
    first, second = Task(example(1, 2)), Task(example(1, 2))
    a, b = first.start(), second.start()
    assert a.sequence == b.sequence and a.request == b.request
    with pytest.raises(RuntimeError):
        first.serve(b, heap)
    assert heap.snapshot() == ()
    first.close()
    second.close()


def test_response_errors_reach_python_exception_handlers():
    async def recover():
        ref = await Request(Op.NEW_DICT)
        try:
            return await Request(Op.DICT_ITEM, ref, 90)
        except KeyError as exc:
            assert exc.args == (90,)
            await Request(Op.DICT_SET, ref, 90, -7)
            return await Request(Op.DICT_ITEM, ref, 90)
    assert run(recover()) == -7


def test_uncaught_errors_are_terminal():
    async def broken():
        return await Request(Op.DICT_ITEM, 5)
    heap, task = Heap(), Task(broken())
    token = task.start()
    result = task.serve(token, heap)
    assert isinstance(result, Failed) and isinstance(result.error, InvalidReference)
    with pytest.raises(RuntimeError):
        task.serve(token, heap)
    with pytest.raises(InvalidReference):
        run(broken())


def test_interleaved_coroutines_share_real_aliases():
    heap = Heap()
    ref = call(heap, Op.NEW_SET)
    async def add(key):
        await Request(Op.SET_ADD, ref, key)
        return await Request(Op.SET_LEN, ref)
    first, second = Task(add(7)), Task(add(7))
    a, b = first.start(), second.start()
    a, b = first.serve(a, heap), second.serve(b, heap)
    assert first.serve(a, heap) == second.serve(b, heap) == Finished(1)


def test_nested_async_helper_is_observable():
    async def helper():
        return await Request(Op.NEW_SET)
    async def outer():
        ref = await helper()
        await Request(Op.SET_ADD, ref, 4)
        return await Request(Op.SET_CONTAINS, ref, 4)
    assert run(outer()) == 1


def test_no_await_completes_immediately_and_cannot_restart():
    async def pure():
        return 7
    task = Task(pure())
    assert task.start() == Finished(7)
    with pytest.raises(RuntimeError):
        task.start()


def test_undeclared_awaitable_is_rejected_and_closed():
    closed = []
    class Unknown:
        def __await__(self):
            yield "undeclared"
    async def bad():
        try:
            await Unknown()
        finally:
            closed.append(True)
    result = Task(bad()).start()
    assert isinstance(result, Failed) and isinstance(result.error, TypeError)
    assert closed == [True]


def test_reentrant_resume_cannot_reuse_current_token():
    heap = Heap()
    async def reenter():
        ref = await Request(Op.NEW_DICT)
        with pytest.raises(RuntimeError):
            task.serve(token, heap)
        return ref
    task = Task(reenter())
    token = task.start()
    assert task.serve(token, heap) == Finished(0)
    assert len(heap.snapshot()) == 1


def test_invalid_response_does_not_consume_token():
    task = Task(example(2, 3))
    token = task.start()
    with pytest.raises(TypeError):
        task.resume(token, 0)
    assert task.observation is token
    task.close()


@pytest.mark.parametrize("values", [dict(value=True), dict(error="unknown"),
                                    dict(value=1, error="keyError", detail=2), dict(detail=3)])
def test_response_schema_rejects_ambiguous_replies(values):
    with pytest.raises((TypeError, ValueError)):
        Response(**values)


def test_allocation_ignores_unused_fields_but_keeps_fresh_ids():
    heap = Heap()
    for i in range(10):
        op = Op.NEW_DICT if i % 2 == 0 else Op.NEW_SET
        assert call(heap, op, -(2**100), 77, -9) == i


def test_new_runtime_does_not_silently_enable_unproved_compilation(tmp_path):
    from zrth.verified import compile_module, UnsupportedPython
    for text in ("async def step(x: int) -> int:\n    return x\n",
                 "def step(values: dict[int, int]) -> int:\n    return values.get(0, 0)\n",
                 "def step(values: set[int]) -> int:\n    return len(values)\n"):
        path = tmp_path / "unsupported.py"
        path.write_text(text)
        with pytest.raises(UnsupportedPython):
            compile_module(path, ["step"])
