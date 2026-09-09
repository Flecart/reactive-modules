"""Contract/export/evidence regressions for direct RM protocol authoring."""
import copy
from pathlib import Path
import sys
import pytest
from zrth import LIA, Int, Var, Module, sugar
from zrth.protocol import (Field, ProtocolModule, PropertySpec, named_module, Simulation,
    ref, lit, op, check, validate_artifact, digest)
from zrth.protocol_check import solver_checks


def register():
    state={"x":Field()}; inputs={"value":Field()}
    module,wires=named_module(state,inputs,lambda s,i:{"x":i["value"]})
    return ProtocolModule("test-register","1",module,wires,state,inputs,("x",))


def test_real_rm_and_initialization():
    p=register(); assert isinstance(p.module,Module)
    sim=Simulation(p.artifact()); assert sim.state=={"x":0}
    assert sim.step(value=2**100)=={"x":2**100}


def test_next_dependency_and_latched_state():
    x,y=Var(Int([1,1])),Var(Int([1,1]))
    class A(sugar.Module):
        def init(self): return 1
        def update(self,x): return x+1
    class B(sugar.Module):
        def init(self,x): return sugar.X(x)+3
        def update(self,y,x): return sugar.X(x)+x
    a=A(theory=LIA,ctrl=(x,)); b=B(theory=LIA,ctrl=(y,),extl=(x,))
    p=ProtocolModule("composed","1",Module.compose(a,b),{"x":x,"y":y},{"x":Field(),"y":Field()}, {},("y",))
    artifact=p.artifact(); assert len(artifact["update"]["blocks"])==2
    sim=Simulation(artifact); assert sim.state=={"x":1,"y":4}
    assert sim.step()=={"x":2,"y":3}


def test_next_external_rejected():
    x,y=Var(Int([1,1])),Var(Int([1,1]))
    class A(sugar.Module):
        def init(self,y): return 0
        def update(self,x,y): return sugar.X(y)
    p=ProtocolModule("unresolved","1",A(theory=LIA,ctrl=(x,),extl=(y,)),{"x":x,"y":y},{"x":Field()},{"y":Field()},())
    with pytest.raises(ValueError,match="unresolved"):p.artifact()


def test_unused_inputs_are_declared():
    state={"x":Field()}; inputs={"ignored":Field()}
    m,w=named_module(state,inputs,lambda s,i:s)
    assert Simulation(ProtocolModule("hold","1",m,w,state,inputs,()).artifact()).step(ignored=9)=={"x":0}


def test_tampering_and_order():
    a=register().artifact(); bad=copy.deepcopy(a); bad["update"]["outputs"]=[-1]
    with pytest.raises(ValueError,match="identity"): validate_artifact(bad)
    bad["sha256"]=digest(bad)
    with pytest.raises(ValueError,match="output index"):validate_artifact(bad)
    bad=copy.deepcopy(a); bad["input_order"]=["other"]; bad["sha256"]=digest(bad)
    with pytest.raises(ValueError,match="order"):validate_artifact(bad)


def test_bad_formula_and_duplicate_properties():
    p=register(); p.properties=(PropertySpec("bad",ref("x")),)
    with pytest.raises(ValueError,match="Boolean"):p.artifact()
    p.properties=(PropertySpec("bad",op("eq",ref("x","next"),lit(0))),)
    with pytest.raises(ValueError,match="reference"):p.artifact()
    p.properties=(PropertySpec("same",lit(True)),)*2
    with pytest.raises(ValueError,match="duplicate"):p.artifact()


def test_bmc_vs_induction():
    p=register(); p.properties=(PropertySpec("always_zero",op("eq",ref("x"),lit(0))),)
    result=solver_checks(p.artifact(),1,2)["always_zero"]
    assert result["z3"]=="reachable-counterexample" and result["depth"]==1
    assert result["induction"]=="not-inductive-unreachable-state-possible"


def test_input_domains():
    p=register(); p.inputs["value"]=Field(minimum=0,maximum=2)
    with pytest.raises(ValueError,match="above"):Simulation(p.artifact()).step(value=3)


def test_stale_source(tmp_path):
    source=tmp_path/"source.py"; source.write_text("version=1")
    p=register(); p.sources=(str(source),); a=p.artifact(); source.write_text("version=2")
    with pytest.raises(ValueError,match="stale"):validate_artifact(a)


def test_lean_negative_witness(tmp_path):
    p=register(); p.properties=(PropertySpec("always_zero",op("eq",ref("x"),lit(0))),)
    result=check(p,"both",directory=tmp_path,depth=1,timeout=10)
    assert result["properties"]["always_zero"]["lean"]=="lean-refuted"


def test_unrelated_theorem_rejected(tmp_path):
    proof=tmp_path/"proof.lean"; proof.write_text("theorem unrelated : True := True.intro\n")
    p=register(); p.properties=(PropertySpec("always_zero",op("eq",ref("x"),lit(0)),proof=str(proof),theorem="unrelated"),)
    with pytest.raises(RuntimeError,match="Lean rejected"):
        check(p,"lean",directory=tmp_path/"evidence")


def test_register_positive_proof(tmp_path):
    sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"verification"/"examples"))
    from protocol_register import build
    result=check(build(),"both",directory=tmp_path,depth=2)
    assert result["properties"]["nonnegative"]["lean"]=="lean-proved"
