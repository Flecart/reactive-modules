"""Reference object-machine runtime for compiled native Python.

Only declared external interfaces can suspend. This runner is not asyncio or a
sandbox for arbitrary host objects; arguments must use the explicit value schema.
"""
from __future__ import annotations

import builtins
from collections import Counter
from dataclasses import dataclass, field
import operator

from .native_frontend import OPS, BUILTINS


@dataclass(eq=False)
class Object:
    kind: str
    fields: dict = field(default_factory=dict)


@dataclass(frozen=True)
class Global:
    name: str


@dataclass(frozen=True)
class Bound:
    value: object
    name: str


@dataclass(frozen=True)
class Deferred:
    target: object
    args: tuple
    keywords: dict


@dataclass(eq=False, frozen=True)
class Pending:
    sequence: int
    interface: str
    receiver: object
    args: tuple
    keywords: dict


@dataclass(frozen=True)
class Finished:
    value: object


@dataclass(frozen=True)
class Failed:
    error: Exception


class InterfaceError(Exception):
    def __init__(self, name, *args):
        self.name = name
        super().__init__(*args)

    def __repr__(self):
        return self.name.rsplit(".", 1)[-1] + "(" + ", ".join(map(repr, self.args)) + ")"

    def __reduce__(self): return type(self), (self.name, *self.args)


UNBOUND = object()
METHODS = {dict: {"get", "copy", "clear"},
           Counter: {"get", "copy", "clear", "most_common"},
           set: {"add", "discard", "remove", "copy", "clear"},
           list: {"append", "copy", "clear"}}


@dataclass
class Frame:
    name: str
    pc: int
    locals: list
    arguments: list
    stack: list = field(default_factory=list)
    attempt: int = 1
    constructor: Object | None = None


@dataclass(eq=False)
class Iterator:
    values: object
    index: int = 0
    size: int = 0


def validate(value, seen=None, active=None):
    """Do not invoke arbitrary __bool__/__getitem__/__repr__ user code."""
    seen = set() if seen is None else seen
    active = set() if active is None else active
    if type(value) is str:
        if any(0xD800 <= ord(c) <= 0xDFFF for c in value):
            raise TypeError("input outside native profile: strings require Unicode scalar values")
        return
    if type(value) in (type(None), int, bool, range): return
    if id(value) in active: raise TypeError("input outside native profile: cyclic object graphs")
    if id(value) in seen: return
    seen.add(id(value))
    active.add(id(value))
    if type(value) in (list, tuple, set):
        for item in value: validate(item, seen, active)
    elif type(value) in (dict, Counter):
        for key, item in value.items(): validate(key, seen, active); validate(item, seen, active)
    elif type(value) is Object:
        for key, item in value.fields.items():
            if type(key) is not str: raise TypeError("object field names must be strings")
            validate(item, seen, active)
    elif type(value) is InterfaceError:
        for item in value.args: validate(item, seen, active)
    else: raise TypeError(f"value type outside native object schema: {type(value).__name__}")
    active.remove(id(value))


class Machine:
    def __init__(self, program, function, arguments, fetch=None):
        for arg in arguments: validate(arg)
        self.program, self.fetch = program, fetch or (lambda pc: program["instructions"][pc])
        self.frames, self.events, self.sequence = [], [], 0
        self.pending = self.result = None
        self.steps = 0
        self.enter(function, list(arguments))

    def enter(self, name, args, keywords=None, constructor=None):
        fn = self.program["functions"][name]
        keywords = keywords or {}
        params = fn["parameters"]
        if len(args) > len(params) or set(keywords) - set(params): raise TypeError("invalid call arguments")
        values = list(args)
        if any(p in keywords for p in params[:len(args)]): raise TypeError("duplicate argument")
        for name_ in params[len(args):]:
            if name_ not in keywords: raise TypeError("missing argument")
            values.append(keywords[name_])
        self.frames.append(Frame(name, fn["entry"], values + [UNBOUND] * (len(fn["locals"])-len(values)),
                                 values, constructor=constructor))

    def suspend(self, interface, receiver, args=(), keywords=None):
        self.pending = Pending(self.sequence, interface, receiver, tuple(args), keywords or {})
        self.events.append(("request", interface, receiver, tuple(args), keywords or {}))

    def error(self, error):
        while self.frames:
            frame = self.frames[-1]
            policy = self.program["functions"][frame.name]["retry"]
            if policy and isinstance(error, InterfaceError) and error.name == policy["exception"] and frame.attempt < policy["tries"]:
                self.suspend("backoff.sleep", None, (frame.attempt, 2 ** (frame.attempt-1)))
                return
            self.frames.pop()
        self.result = Failed(error)

    def resume(self, token, value=None, error=None):
        self.receive(token, value, error)
        return self.run()

    def receive(self, token, value=None, error=None):
        """Apply one external reply without executing subsequent instructions."""
        if self.pending is None or token is not self.pending: raise RuntimeError("stale or foreign suspension")
        if error is not None and not isinstance(error, InterfaceError):
            raise TypeError("external failures require a declared InterfaceError")
        validate(value)
        if error is not None: validate(error)
        self.pending = None
        self.sequence += 1
        if error is not None:
            # Delay is outside the decorated body's exception handler.
            if token.interface == "backoff.sleep": self.frames.pop()
            self.error(error)
        elif token.interface == "backoff.sleep":
            frame = self.frames[-1]
            fn = self.program["functions"][frame.name]
            frame.pc, frame.stack = fn["entry"], []
            frame.locals = frame.arguments + [UNBOUND] * (len(fn["locals"])-len(frame.arguments))
            frame.attempt += 1
        else: self.frames[-1].stack.append(value)

    def invoke(self, target, args, keywords, awaiting=False):
        if isinstance(target, Global):
            name = target.name
            if name in self.program["classes"]:
                obj = Object(name)
                init = self.program["classes"][name].get("__init__")
                if init: self.enter(init, [obj, *args], keywords, constructor=obj); return UNBOUND
                if args or keywords: raise TypeError("constructor takes no arguments")
                return obj
            if name in self.program["functions"]:
                if self.program["functions"][name]["asynchronous"] and not awaiting:
                    return Deferred(target, tuple(args), keywords)
                self.enter(name, args, keywords); return UNBOUND
            interface = self.program["interfaces"].get(name)
            if interface == "exception": return InterfaceError(name, *args)
            if interface == "record":
                if args: raise TypeError("interface record construction requires field keywords")
                return Object(name, dict(keywords))
            if name == "collections.Counter": return Counter(*args, **keywords)
            if name == "print":
                if keywords: raise TypeError("print keyword arguments unsupported")
                self.events.append(("print", " ".join(map(str, args)) + "\n")); return None
            if name in BUILTINS: return getattr(builtins, name)(*args, **keywords)
            raise TypeError("global is not callable")
        if isinstance(target, Bound):
            obj, name = target.value, target.name
            if isinstance(obj, Object):
                methods = self.program["classes"].get(obj.kind, {})
                if name in methods: return self.invoke(Global(methods[name]), [obj, *args], keywords, awaiting)
                declared = self.program["interfaces"].get(obj.kind)
                if isinstance(declared, dict) and name in declared.get("async_methods", []):
                    if not awaiting: return Deferred(target, tuple(args), keywords)
                    self.suspend(obj.kind + "." + name, obj, args, keywords); return UNBOUND
                raise AttributeError(name)
            if name not in METHODS.get(type(obj), set()): raise AttributeError(name)
            value = getattr(obj, name)(*args, **keywords)
            return value
        raise TypeError("value is not callable")

    def step(self):
        if self.pending is not None or self.result is not None: return
        frame = self.frames[-1]
        op, a, b = self.fetch(frame.pc)
        frame.pc += 1
        self.steps += 1
        stack = frame.stack
        pool = self.program["pool"]
        constant = lambda i: pool[i][1]
        popn = lambda n: [stack.pop() for _ in range(n)][::-1]
        try:
            match OPS[op]:
                case "const": stack.append(constant(a))
                case "global": stack.append(Global(constant(a)))
                case "load":
                    value = frame.locals[a]
                    if value is UNBOUND: raise UnboundLocalError(self.program["functions"][frame.name]["locals"][a])
                    stack.append(value)
                case "store": frame.locals[a] = stack.pop()
                case "pop": stack.pop()
                case "dup": stack.append(stack[-1])
                case "dup2": stack.extend(stack[-2:])
                case "swap": stack[-2:] = stack[-2:][::-1]
                case "attr":
                    obj, name = stack.pop(), constant(a)
                    if isinstance(obj, Object) and name in obj.fields: stack.append(obj.fields[name])
                    else:
                        methods = self.program["classes"].get(obj.kind, {}) if isinstance(obj, Object) else METHODS.get(type(obj), set())
                        declaration = self.program["interfaces"].get(obj.kind, {}) if isinstance(obj, Object) else {}
                        external = declaration.get("async_methods", []) if isinstance(declaration, dict) else []
                        if name not in methods and name not in external: raise AttributeError(name)
                        stack.append(Bound(obj, name))
                case "setattr":
                    obj, value = stack.pop(), stack.pop()
                    if not isinstance(obj, Object): raise AttributeError(constant(a))
                    obj.fields[constant(a)] = value
                case "item":
                    key, obj = stack.pop(), stack.pop(); stack.append(obj[key])
                case "setitem":
                    key, obj, value = stack.pop(), stack.pop(), stack.pop(); obj[key] = value
                case "delitem":
                    key, obj = stack.pop(), stack.pop(); del obj[key]
                case "binary":
                    right, left = stack.pop(), stack.pop(); name = constant(a)
                    if name == "in": value = left in right
                    elif name == "notin": value = left not in right
                    elif name == "is": value = left is right
                    elif name == "isnot": value = left is not right
                    else: value = getattr(operator, name)(left, right)
                    stack.append(value)
                case "unary":
                    value = stack.pop(); name = constant(a)
                    stack.append(not value if name == "not" else -value if name == "neg" else +value)
                case "build":
                    name = constant(a); values = popn(b * 2 if name == "dict" else b)
                    stack.append(dict(zip(values[::2], values[1::2])) if name == "dict" else
                                 {"list": list, "tuple": tuple, "set": set}[name](values))
                case "call":
                    names = constant(b); values = popn(a + len(names)); target = stack.pop()
                    if len(set(names)) != len(names): raise TypeError("duplicate keyword")
                    value = self.invoke(target, values[:a], dict(zip(names, values[a:])))
                    if value is not UNBOUND: stack.append(value)
                case "await":
                    deferred = stack.pop()
                    if not isinstance(deferred, Deferred): raise TypeError("await requires an async call")
                    value = self.invoke(deferred.target, list(deferred.args), deferred.keywords, awaiting=True)
                    if value is not UNBOUND: stack.append(value)
                case "return":
                    value = stack.pop()
                    self.frames.pop()
                    if frame.constructor is not None:
                        if value is not None: raise TypeError("__init__ must return None")
                        value = frame.constructor
                    if self.frames: self.frames[-1].stack.append(value)
                    else: self.result = Finished(value)
                case "jump": frame.pc = a
                case "branch":
                    if not stack.pop(): frame.pc = a
                case "unpack":
                    values = list(stack.pop())
                    if len(values) != a: raise ValueError("unpack arity")
                    stack.extend(reversed(values))
                case "format":
                    value = stack.pop(); stack.append(repr(value) if a == 114 else ascii(value) if a == 97 else str(value))
                case "join": stack.append("".join(popn(a)))
                case "raise":
                    value = stack.pop()
                    if not isinstance(value, Exception): raise TypeError("exceptions must derive from BaseException")
                    raise value
                case "iter":
                    value = stack.pop()
                    if type(value) not in (tuple, list, range, dict, Counter): raise TypeError("unsupported iterator schema")
                    stack.append(Iterator(value, size=len(value)))
                case "next":
                    it = stack.pop()
                    if isinstance(it.values, dict) and len(it.values) != it.size: raise RuntimeError("dictionary changed size during iteration")
                    values = list(it.values) if isinstance(it.values, dict) else it.values
                    if it.index >= len(values): frame.pc = a
                    else: stack.append(values[it.index]); it.index += 1
                case _: raise ValueError("unsupported instruction")
        except Exception as error:
            self.error(error)

    def run(self, *, fuel=None):
        """Fuel only pauses execution; exhaustion never means successful return."""
        used = 0
        while self.pending is None and self.result is None and (fuel is None or used < fuel):
            self.step(); used += 1
        return self.pending or self.result
