"""Stop-and-wait channel handlers. The caller executes the returned effects.

Ticks retry a pending request. Sequence numbers do not wrap. The network can
lose, duplicate and reorder genuine packets; no crash or forged-message claim.
"""
from dataclasses import dataclass
from enum import Enum


class EventKind(Enum):
    SUBMIT = 0
    TICK = 1
    ACK = 2


@dataclass(frozen=True)
class Sender:
    sequence: int
    busy: bool
    value: int


@dataclass(frozen=True)
class Event:
    kind: EventKind
    number: int
    value: int


@dataclass(frozen=True)
class SenderEffects:
    send: bool
    number: int
    value: int
    accepted: bool
    completed: bool


@dataclass(frozen=True)
class Receiver:
    expected: int


@dataclass(frozen=True)
class Packet:
    number: int
    value: int


@dataclass(frozen=True)
class ReceiverEffects:
    ack: bool
    number: int
    deliver: bool
    value: int


def initial_sender() -> Sender:
    return Sender(0, False, 0)


def initial_receiver() -> Receiver:
    return Receiver(0)


def sender(state: Sender, event: Event) -> tuple[Sender, SenderEffects]:
    if event.kind == EventKind.SUBMIT:
        if not state.busy:
            return Sender(state.sequence, True, event.value), SenderEffects(True, state.sequence, event.value, True, False)
    if event.kind == EventKind.TICK:
        if state.busy:
            return state, SenderEffects(True, state.sequence, state.value, False, False)
    if event.kind == EventKind.ACK:
        if state.busy and event.number == state.sequence:
            return Sender(state.sequence + 1, False, state.value), SenderEffects(False, 0, 0, False, True)
    return state, SenderEffects(False, 0, 0, False, False)


def receiver(state: Receiver, packet: Packet) -> tuple[Receiver, ReceiverEffects]:
    if packet.number == state.expected:
        return Receiver(state.expected + 1), ReceiverEffects(True, packet.number, True, packet.value)
    if packet.number < state.expected:
        return state, ReceiverEffects(True, packet.number, False, 0)
    return state, ReceiverEffects(False, 0, False, 0)
