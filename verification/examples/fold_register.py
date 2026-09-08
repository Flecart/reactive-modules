"""A reusable helper and an ordinary fixed-tuple loop, without RM annotations."""
from dataclasses import dataclass


@dataclass(frozen=True)
class State:
    value: int


def higher(current: int, offered: int) -> int:
    if offered > current:
        return offered
    return current


def step(state: State, offers: tuple[int, int, int]) -> State:
    value = state.value
    for offered in offers:
        value = higher(value, offered)
    return State(value)
