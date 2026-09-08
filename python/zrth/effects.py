"""Unbounded integer containers and observable async effects.

This is an executable reference service, not yet Python-to-RM container lowering.
Only exact integer keys/values are supported; no capacity, integer, or step bound
is imposed. References preserve aliases. Set iteration is intentionally absent.
"""
from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum
import inspect


class Operation(IntEnum):
    NEW_DICT = 0
    NEW_SET = 1
    DICT_SET = 2
    DICT_GET = 3
    DICT_CONTAINS = 4
    DICT_LEN = 5
    DICT_DELETE = 6
    DICT_COPY = 7
    DICT_KEY_AT = 8
    SET_ADD = 9
    SET_DISCARD = 10
    SET_CONTAINS = 11
    SET_LEN = 12
    SET_REMOVE = 13
    SET_COPY = 14
    DICT_ITEM = 15
    DICT_CLEAR = 16
    SET_CLEAR = 17


class InvalidReference(LookupError):
    pass


class WrongKind(TypeError):
    pass


@dataclass(frozen=True)
class Response:
    value: int = 0
    error: str | None = None
    detail: int = 0

    def __post_init__(self):
        if type(self.value) is not int or type(self.detail) is not int:
            raise TypeError("responses require exact integers")
        if self.error not in (None, "invalidReference", "wrongKind", "keyError", "indexError"):
            raise ValueError("unknown effect error")
        if self.error is None and self.detail != 0 or self.error is not None and self.value != 0:
            raise ValueError("noncanonical response")

    def unwrap(self):
        if self.error is None:
            return self.value
        exception = {"invalidReference": InvalidReference, "wrongKind": WrongKind,
                     "keyError": KeyError, "indexError": IndexError}[self.error]
        raise exception(self.detail)


@dataclass(frozen=True)
class Request:
    operation: Operation
    reference: int = 0
    key: int = 0
    value: int = 0

    def __post_init__(self):
        if type(self.operation) is not Operation:
            raise TypeError("operation must be an Operation member")
        if any(type(v) is not int for v in (self.reference, self.key, self.value)):
            raise TypeError("container references, keys and values require exact integers")

    def __await__(self):
        response = yield self
        if type(response) is not Response:
            raise TypeError("effects must resume with a Response")
        return response.unwrap()


class Heap:
    """A mutable service owning dictionaries and sets, addressed by stable IDs."""

    def __init__(self):
        self._objects: list[dict[int, int] | set[int]] = []

    def snapshot(self):
        """Immutable observation; dictionary order is visible, set order is not."""
        return tuple(("dict", tuple(obj.items())) if type(obj) is dict else
                     ("set", frozenset(obj)) for obj in self._objects)

    def _allocate(self, obj):
        reference = len(self._objects)
        self._objects.append(obj)
        return reference

    def _execute(self, request):
        op, ref, key, value = request.operation, request.reference, request.key, request.value
        if op == Operation.NEW_DICT:
            return self._allocate({})
        if op == Operation.NEW_SET:
            return self._allocate(set())
        if not 0 <= ref < len(self._objects):
            raise InvalidReference(ref)
        obj = self._objects[ref]
        dictionary_ops = {Operation.DICT_SET, Operation.DICT_GET, Operation.DICT_CONTAINS,
                          Operation.DICT_LEN, Operation.DICT_DELETE, Operation.DICT_COPY,
                          Operation.DICT_KEY_AT, Operation.DICT_ITEM, Operation.DICT_CLEAR}
        if (op in dictionary_ops) != (type(obj) is dict):
            raise WrongKind(ref)
        if op == Operation.DICT_SET:
            obj[key] = value
        elif op == Operation.DICT_GET:
            return obj.get(key, value)
        elif op == Operation.DICT_ITEM:
            return obj[key]
        elif op in (Operation.DICT_CONTAINS, Operation.SET_CONTAINS):
            return int(key in obj)
        elif op in (Operation.DICT_LEN, Operation.SET_LEN):
            return len(obj)
        elif op == Operation.DICT_DELETE:
            del obj[key]
        elif op in (Operation.DICT_COPY, Operation.SET_COPY):
            return self._allocate(obj.copy())
        elif op == Operation.DICT_KEY_AT:
            try:
                return tuple(obj)[key]
            except IndexError:
                raise IndexError(key) from None
        elif op == Operation.SET_ADD:
            obj.add(key)
        elif op == Operation.SET_DISCARD:
            obj.discard(key)
        elif op == Operation.SET_REMOVE:
            obj.remove(key)
        elif op in (Operation.DICT_CLEAR, Operation.SET_CLEAR):
            obj.clear()
        else:
            raise AssertionError("unhandled Operation member")
        return 0

    def apply(self, request: Request) -> Response:
        if type(request) is not Request:
            raise TypeError("expected Request")
        try:
            return Response(self._execute(request))
        except (InvalidReference, WrongKind, KeyError, IndexError) as exc:
            name = {InvalidReference: "invalidReference", WrongKind: "wrongKind",
                    KeyError: "keyError", IndexError: "indexError"}[type(exc)]
            return Response(error=name, detail=exc.args[0])


@dataclass(frozen=True, eq=False)
class Pending:
    """An identity-based, single-use token belonging to exactly one task."""
    sequence: int
    request: Request


@dataclass(frozen=True)
class Finished:
    value: object


@dataclass(frozen=True)
class Failed:
    error: BaseException


_RUNNING = object()


class Task:
    """Drive a real Python coroutine one declared effect at a time.

    No asyncio scheduling, I/O, fairness, or crash/restart guarantee is implied.
    Undeclared yielded effects are rejected. close() is explicit cancellation, outside
    the formal transition model.
    """

    def __init__(self, coroutine):
        if not inspect.iscoroutine(coroutine):
            raise TypeError("expected a Python coroutine")
        self._coroutine = coroutine
        self._observation = None
        self._sequence = 0

    @property
    def observation(self):
        return self._observation

    def _advance(self, response):
        # Consume the old token before user code runs, including reentrant code.
        self._observation = _RUNNING
        try:
            request = self._coroutine.send(response)
        except StopIteration as end:
            self._observation = Finished(end.value)
        except Exception as exc:
            self._observation = Failed(exc)
        else:
            if type(request) is not Request:
                try:
                    self._coroutine.close()
                finally:
                    self._observation = Failed(TypeError("coroutine yielded an undeclared effect"))
            else:
                self._observation = Pending(self._sequence, request)
        return self._observation

    def start(self):
        if self._observation is not None:
            raise RuntimeError("task already started")
        return self._advance(None)

    def _validate(self, pending):
        if type(pending) is not Pending or pending is not self._observation:
            raise RuntimeError("stale, foreign, or forged suspension token")

    def resume(self, pending: Pending, response: Response):
        self._validate(pending)
        if type(response) is not Response:
            raise TypeError("expected Response")
        self._sequence += 1
        return self._advance(response)

    def serve(self, pending: Pending, heap: Heap):
        # Check before applying the operation: replay must not mutate the heap.
        self._validate(pending)
        return self.resume(pending, heap.apply(pending.request))

    def close(self):
        self._coroutine.close()
        if not isinstance(self._observation, (Finished, Failed)):
            self._observation = Failed(RuntimeError("task closed"))


def run(coroutine, heap=None):
    """Convenience serial driver; use Task directly to choose interleavings."""
    heap = Heap() if heap is None else heap
    task = Task(coroutine)
    try:
        observation = task.start()
        while isinstance(observation, Pending):
            observation = task.serve(observation, heap)
        if isinstance(observation, Failed):
            raise observation.error
        return observation.value
    finally:
        task.close()
