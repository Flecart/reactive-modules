"""Direct async source for the compiler's declared heap-effect interface."""
from zrth.effects import Operation as Op, Request


async def step(key: int, value: int) -> int:
    reference = await Request(Op.NEW_DICT)
    await Request(Op.DICT_SET, reference, key, value)
    result = await Request(Op.DICT_ITEM, reference, key)
    return result
