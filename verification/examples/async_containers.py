"""Runnable effect-interface example, NOT yet accepted by zrth.verified.

Each Request is an observable suspension. Task lets a caller choose when to
respond and how to interleave tasks sharing a Heap; run is a serial convenience.
"""
from zrth.effects import Operation as Op, Request, run


async def store(dictionary: int, seen: int, key: int, value: int) -> int:
    await Request(Op.DICT_SET, dictionary, key, value)
    await Request(Op.SET_ADD, seen, key)
    return await Request(Op.DICT_ITEM, dictionary, key)


async def example() -> tuple[int, int, int]:
    dictionary = await Request(Op.NEW_DICT)
    seen = await Request(Op.NEW_SET)
    await store(dictionary, seen, 5, 10)
    copied = await Request(Op.DICT_COPY, dictionary)
    await store(dictionary, seen, 5, 20)
    previous = await Request(Op.DICT_ITEM, copied, 5)
    current = await Request(Op.DICT_ITEM, dictionary, 5)
    count = await Request(Op.SET_LEN, seen)
    return previous, current, count


if __name__ == "__main__":
    print(run(example()))  # (10, 20, 1)
