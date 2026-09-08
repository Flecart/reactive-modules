"""Deliberately incorrect fixture: verification must preserve and expose the bug."""
from dataclasses import dataclass


@dataclass(frozen=True)
class State:
    value: int


def step(state: State, offered: int) -> State:
    if offered < state.value:
        return State(offered)
    return state
