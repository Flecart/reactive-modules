"""A second RM-native protocol using the same contract, runner and backends."""
from pathlib import Path
from zrth.protocol import Field, PropertySpec, ProtocolModule, named_module, ref, lit, op
from zrth.expr import ite


def build():
    state={"value":Field(minimum=0)}
    inputs={"write":Field(False,"bool"),"offered":Field(minimum=0)}
    module,wires=named_module(state,inputs,lambda s,i:{"value":ite(i["write"],i["offered"],s["value"])})
    proof=str(Path(__file__).resolve().parents[1]/"proofs"/"protocol_register.lean")
    properties=(PropertySpec("nonnegative",op("ge",ref("value"),lit(0)),proof=proof,theorem="Register.nonnegative"),)
    return ProtocolModule("register","1",module,wires,state,inputs,("value",),properties,sources=(__file__,))
