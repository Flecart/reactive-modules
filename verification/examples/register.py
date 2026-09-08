"""An ordinary Python library; this file contains no RM or Lean constructs."""
from dataclasses import dataclass


@dataclass(frozen=True)
class State:
    value: int


def initial() -> State:
    return State(0)


def step(state: State, offered: int) -> State:
    if offered > state.value:
        return State(offered)
    return state
