"""Native container syntax and nested async calls, without a protocol adapter."""
from collections import Counter


async def increment(value):
    return value + 1


async def step(limit):
    values = {}
    seen = set()
    counts = Counter()
    for number in range(limit):
        values[number] = await increment(number)
        seen.add(values[number])
        counts["visits"] += 1
    return (values, len(seen), counts["visits"])
