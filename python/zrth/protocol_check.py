"""Independent evidence engines for one RM-native artifact.

SMT results are diagnostic, never imported as axioms. Lean proof files must
inhabit the generated obligation type; theorem names alone confer no status.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess

from .protocol import validate_artifact, run_graph
from .verified_backend import evaluate, lean_expr, lean_list, project_root, audit_axioms


def zexpr(e, env):
    import z3
    match e:
        case ["var", i]: return env[i]
        case ["lit", v]: return z3.IntVal(v)
        case ["boolean", v]: return z3.BoolVal(v)
        case ["not", a]: return z3.Not(zexpr(a,env))
        case ["ite", c, a, b]: return z3.If(zexpr(c,env),zexpr(a,env),zexpr(b,env))
        case ["bin", operator, a, b]:
            x,y=zexpr(a,env),zexpr(b,env)
            return {"add":lambda:x+y,"sub":lambda:x-y,"eq":lambda:x==y,"ne":lambda:x!=y,
                    "lt":lambda:x<y,"le":lambda:x<=y,"gt":lambda:x>y,"ge":lambda:x>=y,
                    "and":lambda:z3.And(x,y),"or":lambda:z3.Or(x,y),"xor":lambda:z3.Xor(x,y)}[operator]()
    raise ValueError("invalid formula")


def zgraph(g, args, solver, prefix):
    import z3
    env=list(args)
    for k,e in enumerate(g["terms"]):
        v=zexpr(e,env)
        wire=z3.Const(f"{prefix}_{k}",v.sort())
        solver.add(wire==v)
        env.append(wire)
    return [env[i] for i in g["outputs"]]


def variables(fields,prefix):
    import z3
    return [(z3.Bool if f["sort"]=="bool" else z3.Int)(f"{prefix}_{k}") for k,f in fields.items()]


def domains(fields, values):
    import z3
    result=[]
    for f,v in zip(fields.values(),values):
        if f["sort"]=="int":
            if f["minimum"] is not None: result.append(v>=f["minimum"])
            if f["maximum"] is not None: result.append(v<=f["maximum"])
    return z3.And(*result)


def concrete(model,values):
    import z3
    return [int(z3.is_true(v)) if z3.is_bool(v) else v.as_long()
            for v in (model.eval(x,model_completion=True) for x in values)]


def solver_checks(a,depth,timeout):
    import z3
    results={p["identifier"]:{"z3":"not-run"} for p in a["properties"]}
    # All properties at each depth share one transition unrolling.
    s=z3.Solver(); s.set(timeout=int(timeout*1000))
    initial=variables(a["inputs"],"initial")
    s.add(domains(a["inputs"],initial))
    states=[zgraph(a["init"],initial,s,"init")]; actions=[]
    for k in range(depth+1):
        for p in a["properties"]:
            result=results[p["identifier"]]
            if result["z3"] in ("reachable-counterexample","reachable-witness","unknown","unsupported"): continue
            if p["kind"]=="leads-to":
                result.update(z3="unsupported",reason="positive temporal SMT checking is not implemented")
                continue
            if p["kind"]=="step" and k==0: continue
            env=states[-2]+actions[-1]+states[-1] if p["kind"]=="step" else states[-1]
            goal=zexpr(p["resolved"],env)
            s.push()
            if p["kind"]=="step": s.add(domains(a["state"],states[-2]))
            s.add(goal if p["kind"]=="reachability" else z3.Not(goal))
            answer=s.check()
            if answer==z3.sat:
                model=s.model()
                result.update(z3="reachable-witness" if p["kind"]=="reachability" else "reachable-counterexample",
                              depth=k,trace={"initial_inputs":concrete(model,initial),
                              "actions":[concrete(model,i) for i in actions],
                              "states":[concrete(model,v) for v in states]})
            elif answer==z3.unknown: result.update(z3="unknown",reason=s.reason_unknown(),depth=k)
            else: result.update(z3="no-counterexample-through-k",depth=k)
            s.pop()
        if k<depth:
            i=variables(a["inputs"],f"input{k}"); s.add(domains(a["inputs"],i)); actions.append(i)
            states.append(zgraph(a["update"],states[-1]+i,s,f"step{k}"))
    # Induction queries deliberately separate from reachable counterexamples.
    for p in a["properties"]:
        if p["kind"] not in ("invariant","step"): continue
        q=z3.Solver(); q.set(timeout=int(timeout*1000))
        state=variables(a["state"],"state"); incoming=variables(a["inputs"],"input")
        q.add(domains(a["inputs"],incoming))
        nxt=zgraph(a["update"],state+incoming,q,"next")
        if p["kind"]=="invariant":
            q.add(zexpr(p["resolved"],state),z3.Not(zexpr(p["resolved"],nxt)))
        else:
            q.add(domains(a["state"],state),z3.Not(zexpr(p["resolved"],state+incoming+nxt)))
        answer=q.check()
        results[p["identifier"]]["induction"]=("solver-unsat" if answer==z3.unsat else
            "not-inductive-unreachable-state-possible" if answer==z3.sat else "unknown")
    return results


def lean_graph(g):
    return f"⟨{g['inputs']}, {lean_list(map(lean_expr,g['terms']))}, {lean_list(map(str,g['outputs']))}⟩"


def lean_domain(fields):
    conditions=[f"v.length = {len(fields)}"]
    for k,f in enumerate(fields.values()):
        x=f"(environment v {k})"
        if f["sort"]=="bool": conditions.append(f"({x} = 0 ∨ {x} = 1)")
        else:
            if f["minimum"] is not None: conditions.append(f"{f['minimum']} ≤ {x}")
            if f["maximum"] is not None: conditions.append(f"{x} ≤ {f['maximum']}")
    return " ∧ ".join(conditions)


def certificate(a):
    lines=["import ReactiveModules.Protocol", "open ReactiveModules ReactiveModules.Protocol",
           "noncomputable section", "set_option linter.all false",
           "namespace ProtocolArtifact", "set_option maxRecDepth 1000000",
           "set_option maxHeartbeats 0", f"-- Artifact SHA256 {a['sha256']}"]
    for phase in ("init","update"):
        g=a[phase]; blocks=[]; cursor=0
        for size in g["blocks"]:
            blocks.append(lean_list(map(lean_expr,g["terms"][cursor:cursor+size]))); cursor+=size
        lines += [f"def {phase}Blocks : List (List Expr) := {lean_list(blocks)}",
                  f"def {phase}Graph : Graph := ⟨{g['inputs']}, {phase}Blocks.flatten, {lean_list(map(str,g['outputs']))}⟩",
                  f"theorem {phase}_execution (env : Nat → Int) :",
                  f"  {phase}Graph.run env = {phase}Graph.outputs.map (rounds {phase}Graph.inputs {phase}Blocks env) :=",
                  f"  graph_blocks_correct {phase}Graph {phase}Blocks rfl env",
                  f"#print axioms {phase}_execution"]
    lines += ["def model : Model := ⟨initGraph, updateGraph⟩",
              f"def inputDomain (v : List Int) : Prop := {lean_domain(a['inputs'])}",
              f"def stateDomain (v : List Int) : Prop := {lean_domain(a['state'])}",
              "instance (v) : Decidable (inputDomain v) := by unfold inputDomain; infer_instance",
              "instance (v) : Decidable (stateDomain v) := by unfold stateDomain; infer_instance"]
    for n,p in enumerate(a["properties"]):
        lines.append(f"def formula{n} : Expr := {lean_expr(p['resolved'])}")
        kind=p["kind"]
        if kind=="invariant": body=f"Invariant model inputDomain formula{n}"
        elif kind=="step": body=f"StepProperty model stateDomain inputDomain formula{n}"
        elif kind=="reachability": body=f"∃ s, Reachable model inputDomain s ∧ formula{n}.eval (environment s) ≠ 0"
        else:
            lines.append(f"def trigger{n} : Expr := {lean_expr(p['resolved_trigger'])}")
            body=f"LeadsTo model inputDomain trigger{n} formula{n}"
        lines.append(f"def obligation{n} : Prop := {body}")
    # Proof data need kernel reduction, not executable code generation.
    return "\n".join(lines+["end ProtocolArtifact",""]).replace("\ndef ","\nnoncomputable def ")


def _lean(directory,name,source,timeout):
    path=directory/f"{name}.lean"; path.write_text(source)
    log=directory/f"{name}.log"
    with log.open("w") as output:
        process=subprocess.Popen(["lake","env","lean","-j1",str(path)],cwd=project_root(),
            text=True,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
        try: process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            # Terminate this check's process group, including lake's Lean child.
            try: os.killpg(process.pid,signal.SIGTERM)
            except ProcessLookupError: pass
            try: process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid,signal.SIGKILL); process.wait()
            raise
    if path.read_text()!=source: raise ValueError("generated proof changed during checking")
    if process.returncode: raise RuntimeError(f"Lean rejected {name} (exit {process.returncode}); see {log}")
    audit_axioms(log.read_text())


def replay(a,trace):
    rows=[trace["initial_inputs"],*trace["actions"],*trace["states"]]
    if "idle" in trace: rows.append(trace["idle"])
    if any(type(row) is not list or any(type(v) is not int for v in row) for row in rows):
        raise ValueError("witnesses must contain encoded integer wire values")
    current=run_graph(a["init"],trace["initial_inputs"])
    if current != trace["states"][0]: raise ValueError("incorrect initial witness")
    for i,expected in zip(trace["actions"],trace["states"][1:],strict=True):
        current=run_graph(a["update"],current+i)
        if current != expected: raise ValueError("incorrect transition witness")


def witness_source(a,p,n,source,trace):
    """Kernel replay plus an actual proof of the specified (negated) obligation."""
    trace=dict(trace)
    if any(type(row) is not list or any(type(v) is not int for v in row)
           for row in [trace["initial_inputs"],*trace["actions"]]):
        raise ValueError("witnesses must contain encoded integer wire values")
    if "states" not in trace:
        states=[run_graph(a["init"],trace["initial_inputs"])]
        for action in trace["actions"]: states.append(run_graph(a["update"],states[-1]+action))
        trace["states"]=states
    replay(a,trace)
    rows=[source,"open ProtocolArtifact", "namespace Witness", "set_option Elab.async false",
          "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0"]
    def progress(label):
        return f"-- Certificate stage: {label}"
    ints=lambda v:lean_list(f"({x})" for x in v)
    rows += [progress("initial input domain"),f"def initialInput : List Int := {ints(trace['initial_inputs'])}",
             "theorem initial_allowed : inputDomain initialInput := by decide"]
    for t,state in enumerate(trace["states"]): rows.append(f"def state{t} : List Int := {ints(state)}")
    def equality(name,phase,args,environment,result,statement,model_args):
        env=list(args)
        for term in a[phase]["terms"]: env.append(evaluate(term,env))
        # Kernel reduction of huge List/Array lookups is expensive. A balanced
        # lookup function supplies exactly the same untrusted numerical values.
        runs=[(k,v) for k,v in enumerate(env) if k==0 or v!=env[k-1]]
        def lookup(rows):
            if len(rows)==1: return f"(.leaf ({rows[0][1]}))"
            middle=len(rows)//2
            return f"(.branch {rows[middle][0]} {lookup(rows[:middle])} {lookup(rows[middle:])})"
        chunks=[a[phase]["terms"][k:k+32] for k in range(0,len(a[phase]["terms"]),32)]
        lines=[progress(name+" values"),f"def {name}Tree : ValueTree := {lookup(runs) if runs else '.leaf 0'}",
               f"def {name}Values : Nat → Int := {name}Tree.lookup"]
        lines.append(f"#print axioms {name}Values")
        for k,chunk in enumerate(chunks):
            if k%64==0: lines.append(progress(f"{name} chunk {k}/{len(chunks)}"))
            lines += [f"def {name}Chunk{k} : List Expr := {lean_list(map(lean_expr,chunk))}",
                      f"theorem {name}Checked{k} : checkedTerms {name}Values {a[phase]['inputs']+32*k} {name}Chunk{k} = true := by decide"]
            if k%64==0: lines.append(f"#print axioms {name}Checked{k}")
        chunk_names=lean_list(f"{name}Chunk{k}" for k in range(len(chunks)))
        proof="True.intro"
        for k in reversed(range(len(chunks))): proof=f"⟨{name}Checked{k}, {proof}⟩"
        lines += [progress(name+" combine chunks"),f"theorem {name}Terms : checkedTerms {name}Values {phase}Graph.inputs {phase}Graph.terms = true :=",
                  "  by",
                  f"    have layout : {chunk_names}.flatten = {phase}Graph.terms := by rfl",
                  "    rw [← layout]",
                  f"    exact checkedBlocks_correct {name}Values {chunk_names} {phase}Graph.inputs ({proof})",
                  f"#print axioms {name}Terms"]
        return lines+[
                progress(name+" complete equation"),
                f"theorem {name}CheckedRun : checkedRun {phase}Graph ({environment}) {name}Values = true := by",
                f"  unfold checkedRun; rw [Bool.and_eq_true, Bool.and_eq_true]; exact ⟨⟨by decide, {name}Terms⟩, by decide⟩",
                f"theorem {name} : {statement} :=",
                f"  {'start' if phase=='init' else 'step'}_checked initGraph updateGraph {model_args} {result} {name}Values {name}CheckedRun (by decide)"]
    rows += equality("initial_eq","init",trace["initial_inputs"],"environment initialInput","state0",
                     "model.start initialInput = state0","initialInput")
    rows += [
             "theorem reachable0 : Reachable model inputDomain state0 := by",
             "  rw [← initial_eq]; exact .initial _ initial_allowed"]
    for t,action in enumerate(trace["actions"]):
        rows += [f"def action{t} : List Int := {ints(action)}",
                 f"theorem allowed{t} : inputDomain action{t} := by decide"]
        rows += equality(f"step{t}","update",trace["states"][t]+action,
                         f"environment (state{t} ++ action{t})",f"state{t+1}",
                         f"model.step state{t} action{t} = state{t+1}",f"state{t} action{t}")
        rows += [
                 f"theorem reachable{t+1} : Reachable model inputDomain state{t+1} := by",
                 f"  rw [← step{t}]; exact .advance _ _ reachable{t} allowed{t}"]
    end=len(trace["actions"])
    kind=p["kind"]
    if kind=="leads-to":
        idle=trace["idle"]
        if run_graph(a["update"],trace["states"][-1]+idle)!=trace["states"][-1]: raise ValueError("not a stuttering lasso")
        rows += [f"def idleInput : List Int := {ints(idle)}"]
        rows += equality("fixed","update",trace["states"][-1]+idle,f"environment (state{end} ++ idleInput)",
                         f"state{end}",f"model.step state{end} idleInput = state{end}",f"state{end} idleInput")
        rows += [
                 f"theorem result : ¬ obligation{n} := idle_refutes model inputDomain trigger{n} formula{n}",
                 f"  state{end} idleInput reachable{end} (by decide) fixed (by decide) (by decide)"]
    elif kind=="invariant":
        if evaluate(p["resolved"],trace["states"][-1]): raise ValueError("witness does not refute invariant")
        rows += [f"theorem result : ¬ obligation{n} := by",
                 f"  intro h; exact (h state{end} reachable{end}) (by decide)"]
    elif kind=="reachability":
        if not evaluate(p["resolved"],trace["states"][-1]): raise ValueError("witness does not establish reachability")
        rows += [f"theorem result : obligation{n} := ⟨state{end}, reachable{end}, by decide⟩"]
    else:
        if not end: raise ValueError("step witness must contain a step")
        rows += [f"theorem result : ¬ obligation{n} := by",
                 f"  intro h; have bad := h state{end-1} action{end-1} (by decide) allowed{end-1}",
                 f"  rw [step{end-1}] at bad; exact bad (by decide)"]
    return ("\n".join(rows+["#print axioms result","end Witness",""])
            .replace("\ndef ","\nnoncomputable def ").replace("by decide","by decide +kernel"))


def check(a,backend="both",*,directory="protocol-evidence",depth=16,timeout=30):
    if backend not in ("z3","lean","both") or depth<0 or timeout<=0: raise ValueError("invalid check options")
    directory=Path(directory).resolve(); directory.mkdir(parents=True,exist_ok=True)
    status={"artifact":a["sha256"],"rm_execution":"not-run","properties":{},"backend":backend}
    status_path=directory/"status.json"
    status_path.write_text(json.dumps(status,indent=2)+"\n")
    validate_artifact(a)
    (directory/"artifact.json").write_text(json.dumps(a,indent=2)+"\n")
    source=certificate(a)
    (directory/"ProtocolArtifact.lean").write_text(source)
    results=({p["identifier"]:{"z3":"not-run"} for p in a["properties"]} if backend=="lean"
             else solver_checks(a,depth,timeout))
    for result in results.values(): result["lean"]="not-run"
    if backend in ("lean","both"):
        build=subprocess.run(["lake","build","ReactiveModules.Protocol"],cwd=project_root(),text=True,capture_output=True,timeout=max(timeout,120))
        if build.returncode: raise RuntimeError(build.stdout+build.stderr)
        _lean(directory,"ProtocolArtifact",source,max(timeout,120))
        status["rm_execution"]="lean-proved"
        for n,p in enumerate(a["properties"]):
            result=results[p["identifier"]]
            if p["proof"]:
                proof=Path(p["proof"]).read_text()
                # No importing a stale artifact with the same module name.
                if re.search(r"\b(import|axiom|sorry|admit|native_decide)\b",proof):
                    raise ValueError("proof snippets cannot import modules or admit proofs")
                theorem=p["theorem"]
                if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*",theorem): raise ValueError("invalid theorem identifier")
                _lean(directory,f"Property{n}",source+"\n"+proof+
                      f"\nexample : ProtocolArtifact.obligation{n} := {theorem}\n#print axioms {theorem}\n",max(timeout,120))
                result.update(lean="lean-proved",proof_sha256=hashlib.sha256(proof.encode()).hexdigest())
            elif p["witness"] or "trace" in result:
                trace=p["witness"] or result["trace"]
                try:
                    _lean(directory,f"Trace{n}",witness_source(a,p,n,source,trace),max(timeout,120))
                    result["lean"]="lean-proved" if p["kind"]=="reachability" else "lean-refuted"
                except subprocess.TimeoutExpired:
                    result.update(lean="unknown",lean_reason="kernel witness checking timed out")
    validate_artifact(a)
    status["properties"]=results
    status_path.write_text(json.dumps(status,indent=2)+"\n")
    return status
