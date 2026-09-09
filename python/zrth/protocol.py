"""Discrete RM-native protocol contracts. No Python-source compiler or object VM.

Author callbacks execute once, symbolically, using the ordinary Expr/Term DSL.
The artifact is read back from actual RM atoms, including initialization.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass, field as dcfield
import hashlib
import json
from pathlib import Path

from . import Bool, Int, LIA, Module, Term, Var, X
from .expr import Expr, collecting, expr, ite
from .verified_backend import evaluate


@dataclass(frozen=True)
class Field:
    initial: int | bool = 0
    sort: str = "int"
    minimum: int | None = None
    maximum: int | None = None
    labels: dict = dcfield(default_factory=dict)

    def __post_init__(self):
        if self.sort not in ("int", "bool"):
            raise ValueError("only scalar Int/Bool fields are supported")
        if self.sort == "bool" and type(self.initial) is not bool:
            raise ValueError("Boolean initial value required")
        if self.sort == "int" and type(self.initial) is not int:
            raise ValueError("integer initial value required")
        if self.minimum is not None and self.maximum is not None and self.minimum > self.maximum:
            raise ValueError("empty field domain")


def ref(name, phase="state"):
    if phase not in ("state", "input", "next"):
        raise ValueError("unknown reference phase")
    return [phase, name]


def lit(value):
    return ["boolean", value] if type(value) is bool else ["lit", value]


def op(operator, left, right):
    return ["bin", operator, left, right]


def conjunction(expressions):
    result = lit(True)
    for e in expressions:
        result = op("and", result, e)
    return result


def disjunction(expressions):
    result = lit(False)
    for e in expressions:
        result = op("or", result, e)
    return result


def implies(a, b):
    return op("or", ["not", a], b)


@dataclass(frozen=True)
class PropertySpec:
    identifier: str
    formula: list
    kind: str = "invariant"
    assumptions: tuple[str, ...] = ()
    trigger: list | None = None
    proof: str | None = None
    theorem: str | None = None
    witness: dict | None = None

    def __post_init__(self):
        if self.kind not in ("invariant", "step", "reachability", "leads-to"):
            raise ValueError("unsupported property kind")
        if self.kind == "leads-to" and self.trigger is None:
            raise ValueError("leads-to requires a trigger")
        if bool(self.proof) != bool(self.theorem):
            raise ValueError("proof file and theorem must be supplied together")


def named_module(state, inputs, update, *, initialize=None, hidden=()):
    """Return a real RM module and its named wires; omitted updates hold state."""
    if set(state) & set(inputs):
        raise ValueError("state/input names overlap")
    wires = {k: Var((Bool if f.sort == "bool" else Int)([1, 1]))
             for k, f in (state | inputs).items()}
    with collecting() as initial:
        values = ({k: f.initial for k, f in state.items()} if initialize is None
                  else initialize({k: expr(wires[k], theory=LIA) for k in inputs}))
        if set(values) != set(state):
            raise ValueError("initialization must drive every controlled field")
        for k, v in values.items():
            e = v if isinstance(v, Expr) else expr(v, theory=LIA, sort=wires[k].dtype)
            initial.append(Term(LIA.Id(), [X(wires[k])], [e.wire]))
    with collecting() as terms:
        current = {k: expr(wires[k], theory=LIA) for k in state}
        incoming = {k: expr(wires[k], theory=LIA) for k in inputs}
        values = update(dict(current), incoming)
        if set(values) - set(state):
            raise ValueError("update drives an undeclared field")
        for k in state:
            v = values.get(k, current[k])
            e = v if isinstance(v, Expr) else expr(v, theory=LIA, sort=wires[k].dtype)
            terms.append(Term(LIA.Id(), [X(wires[k])], [e.wire]))
    if set(hidden) - set(state):
        raise ValueError("only controlled fields may be hidden")
    return Module(init=initial, update=terms, vars=list(wires.values()),
                  hide={wires[k] for k in hidden}), wires


def _sort(wire):
    match wire.dtype:
        case Int(shape) if list(shape) == [1, 1]: return "int"
        case Bool(shape) if list(shape) == [1, 1]: return "bool"
        case _: raise ValueError("only scalar Int/Bool wires are supported")


def _export(module, wires, state, inputs, phase):
    # Current-state wires are unavailable during initialization. Next external
    # wires are intentionally unsupported: this API samples latched inputs.
    names = list(inputs) if phase == "init" else list(state) + list(inputs)
    index = {wires[k]: i for i, k in enumerate(names)}
    sorts = [(_sort(wires[k])) for k in names]
    terms, blocks = [], []
    inverse = {"LIA_" + v: k for k, v in dict(add="Add", sub="Sub", eq="Eq",
        ne="Ne", lt="Lt", le="Le", gt="Gt", ge="Ge", xor="Xor",
        **{"and": "And", "or": "Or"}).items()}
    for atom in module.atoms:
        start = len(terms)
        block = getattr(atom, phase if phase == "init" else "update")
        for term in block:
            if len(term.write) != 1 or term.write[0] in index:
                raise ValueError("duplicate or nonscalar RM controller")
            if any(w not in index for w in term.read):
                raise ValueError("unresolved current/next dependency")
            args = [["var", index[w]] for w in term.read]
            match term.itype:
                case LIA.Int(t): value = ["lit", int(t.item())]
                case LIA.Bool(t): value = ["boolean", bool(t.item())]
                case LIA.Id(): value = args[0]
                case LIA.Not(): value = ["not", *args]
                case LIA.Ite(): value = ["ite", *args]
                case _:
                    tag = type(term.itype).__name__
                    if tag not in inverse or len(args) != 2:
                        raise ValueError(f"unsupported discrete RM operator {tag}")
                    value = ["bin", inverse[tag], *args]
            expected = _sort(term.write[0])
            if expression_sort(value, sorts) != expected:
                raise ValueError("ill-typed exported RM term")
            index[term.write[0]] = len(names) + len(terms)
            sorts.append(expected)
            terms.append(value)
        blocks.append(len(terms) - start)
    try:
        outputs = [index[X(wires[k])] for k in state]
    except KeyError as e:
        raise ValueError("incomplete RM state transition") from e
    return dict(inputs=len(names), terms=terms, outputs=outputs, blocks=blocks,
                input_sorts=sorts[:len(names)], output_sorts=[state[k].sort for k in state])


def expression_sort(e, sorts):
    match e:
        case ["var", i] if type(i) is int and 0 <= i < len(sorts): return sorts[i]
        case ["lit", n] if type(n) is int: return "int"
        case ["boolean", b] if type(b) is bool: return "bool"
        case ["not", a] if expression_sort(a, sorts) == "bool": return "bool"
        case ["ite", c, a, b]:
            sa, sb = expression_sort(a, sorts), expression_sort(b, sorts)
            if expression_sort(c, sorts) == "bool" and sa == sb: return sa
        case ["bin", operator, a, b]:
            sa, sb = expression_sort(a, sorts), expression_sort(b, sorts)
            if sa != sb: raise ValueError("mixed operand types")
            if operator in ("add", "sub") and sa == "int": return "int"
            if operator in ("lt", "le", "gt", "ge") and sa == "int": return "bool"
            if operator in ("and", "or", "xor") and sa == "bool": return "bool"
            if operator in ("eq", "ne"): return "bool"
    raise ValueError(f"invalid/unsupported expression {e}")


def resolve(e, state, inputs, *, allow_next=False, allow_input=False):
    match e:
        case ["state", n]: return ["var", list(state).index(n)]
        case ["input", n] if allow_input: return ["var", len(state) + list(inputs).index(n)]
        case ["next", n] if allow_next:
            return ["var", len(state) + len(inputs) + list(state).index(n)]
        case ["lit" | "boolean", _]: return e
        case ["bin", o, a, b]:
            return ["bin", o, resolve(a, state, inputs, allow_next=allow_next, allow_input=allow_input),
                    resolve(b, state, inputs, allow_next=allow_next, allow_input=allow_input)]
        case ["not", a]: return ["not", resolve(a, state, inputs, allow_next=allow_next, allow_input=allow_input)]
        case ["ite", c, a, b]:
            return ["ite", *[resolve(v, state, inputs, allow_next=allow_next, allow_input=allow_input) for v in (c,a,b)]]
    raise ValueError(f"invalid formula reference {e}")


@dataclass
class ProtocolModule:
    identifier: str
    version: str
    module: object
    wires: dict
    state: dict[str, Field]
    inputs: dict[str, Field]
    outputs: tuple[str, ...]
    properties: tuple[PropertySpec, ...] = ()
    assumptions: dict[str, str] = dcfield(default_factory=dict)
    profile: dict = dcfield(default_factory=dict)
    sources: tuple[str, ...] = ()

    def artifact(self):
        if set(self.wires) != set(self.state) | set(self.inputs):
            raise ValueError("wire bindings differ from contract")
        if len(set(self.wires.values())) != len(self.wires):
            raise ValueError("aliased field bindings")
        if set(self.module.ctrl) != {self.wires[k] for k in self.state}:
            raise ValueError("RM controllers differ from declared state")
        if not set(self.module.extl) <= {self.wires[k] for k in self.inputs}:
            raise ValueError("RM external interface differs from contract")
        if set(self.outputs) - set(self.state):
            raise ValueError("unknown output")
        if any(self.wires[k] not in set(self.module.intf) for k in self.outputs):
            raise ValueError("output is hidden")
        if len({p.identifier for p in self.properties}) != len(self.properties):
            raise ValueError("duplicate property identifier")
        for atom in self.module.atoms:
            if any(type(t.itype).__name__ != "Differential_ZERO" for t in atom.delay):
                raise ValueError("nontrivial continuous dynamics are not supported")
        props = []
        sorts = [f.sort for f in self.state.values()] + [f.sort for f in self.inputs.values()] + [f.sort for f in self.state.values()]
        for p in self.properties:
            if set(p.assumptions) - set(self.assumptions):
                raise ValueError("unknown property assumption")
            step = p.kind == "step"
            formula = resolve(p.formula, self.state, self.inputs, allow_next=step, allow_input=step)
            if expression_sort(formula, sorts) != "bool":
                raise ValueError("property must be Boolean")
            trigger = resolve(p.trigger, self.state, self.inputs) if p.trigger is not None else None
            if trigger is not None and expression_sort(trigger, sorts) != "bool":
                raise ValueError("trigger must be Boolean")
            props.append(asdict(p) | dict(resolved=formula, resolved_trigger=trigger))
        a = dict(format="zrth.protocol.v1", identifier=self.identifier, version=self.version,
                 state_order=list(self.state), input_order=list(self.inputs),
                 state={k: asdict(f) for k,f in self.state.items()},
                 inputs={k: asdict(f) for k,f in self.inputs.items()}, outputs=list(self.outputs),
                 assumptions=self.assumptions, profile=self.profile, properties=props,
                 init=_export(self.module,self.wires,self.state,self.inputs,"init"),
                 update=_export(self.module,self.wires,self.state,self.inputs,"update"),
                 sources={str(Path(p).resolve()): hashlib.sha256(Path(p).read_bytes()).hexdigest()
                          for p in (*self.sources, *(p.proof for p in self.properties if p.proof))},
                 tooling=tooling(),
                 trust=["symbolic construction", "RM export", "profile correspondence to deployment"],
                 semantics="mathematical integers; ordered discrete RM atoms")
        a["sha256"] = digest(a)
        return a


def digest(artifact):
    return hashlib.sha256(json.dumps({k:v for k,v in artifact.items() if k != "sha256"},
                                    sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def tooling():
    from .verified_backend import project_root
    root=project_root()
    paths=[Path(__file__), Path(__file__).with_name("protocol_check.py"), Path(__file__).with_name("protocol_layout.py"),
           root/"ReactiveModules"/"Protocol.lean", root/"ReactiveModules"/"Compiler.lean",
           root/"lean-toolchain", root/"lakefile.toml", root/"lake-manifest.json"]
    return {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def validate_artifact(a):
    if a.get("sha256") != digest(a): raise ValueError("artifact identity mismatch")
    if a.get("tooling") != tooling(): raise ValueError("stale verification tooling")
    if list(a["state"]) != a["state_order"] or list(a["inputs"]) != a["input_order"]:
        raise ValueError("field order differs from contract")
    for phase in ("init", "update"):
        g = a[phase]
        sorts = list(g["input_sorts"])
        fields=list(a["inputs"].values()) if phase=="init" else list(a["state"].values())+list(a["inputs"].values())
        if sorts != [f["sort"] for f in fields]: raise ValueError("incorrect input sorts")
        if any(type(n) is not int or n<0 for n in g["blocks"]): raise ValueError("invalid atom boundaries")
        if len(sorts) != g["inputs"] or sum(g["blocks"]) != len(g["terms"]):
            raise ValueError("invalid graph layout")
        for e in g["terms"]: sorts.append(expression_sort(e, sorts))
        if any(type(i) is not int or not 0<=i<len(sorts) for i in g["outputs"]): raise ValueError("invalid output index")
        if len(g["outputs"]) != len(a["state"]) or [sorts[i] for i in g["outputs"]] != g["output_sorts"]:
            raise ValueError("invalid graph outputs")
        if g["output_sorts"] != [f["sort"] for f in a["state"].values()]: raise ValueError("incorrect output sorts")
    for p in a["properties"]:
        step=p["kind"]=="step"
        if p["resolved"] != resolve(p["formula"],a["state"],a["inputs"],allow_next=step,allow_input=step):
            raise ValueError("property reference binding mismatch")
    for path, expected in a["sources"].items():
        if hashlib.sha256(Path(path).read_bytes()).hexdigest() != expected:
            raise ValueError("stale source provenance; rebuild protocol")


def run_graph(g, arguments):
    if len(arguments) != g["inputs"]: raise ValueError("graph input arity")
    env = list(arguments)
    for term in g["terms"]: env.append(evaluate(term, env))
    return [env[i] for i in g["outputs"]]


class Simulation:
    def __init__(self, artifact, initial_inputs=None):
        validate_artifact(artifact)
        self.artifact = artifact
        initial_inputs = initial_inputs or {k:f["initial"] for k,f in artifact["inputs"].items()}
        self.state = dict(zip(artifact["state"], run_graph(artifact["init"], self._inputs(initial_inputs))))

    def _inputs(self, values):
        if set(values) != set(self.artifact["inputs"]): raise ValueError("input fields differ")
        for k,f in self.artifact["inputs"].items():
            v = values[k]
            if type(v) is not (bool if f["sort"] == "bool" else int): raise ValueError("input type")
            if f["minimum"] is not None and v < f["minimum"]: raise ValueError("input below domain")
            if f["maximum"] is not None and v > f["maximum"]: raise ValueError("input above domain")
        return list(values[k] for k in self.artifact["inputs"])

    def step(self, **inputs):
        values = run_graph(self.artifact["update"], list(self.state.values()) + self._inputs(inputs))
        self.state = dict(zip(self.artifact["state"], values))
        return dict(self.state)


def check(protocol, backend="both", *, directory="protocol-evidence", depth=16, timeout=30):
    from .protocol_check import check as check_artifact
    return check_artifact(protocol.artifact(), backend, directory=directory, depth=depth, timeout=timeout)
