# RM-native protocol contracts

`zrth.protocol` is an additional, direct RM authoring route. It does not inspect
Python source and does not use the native object/async VM. Existing `verified`,
`verified_async`, and `verified_native` entrypoints are unchanged.

## Authoring

```python
from zrth.protocol import (
    Field, ProtocolModule, PropertySpec, named_module, ref, lit, op, check,
)

state = {"value": Field()}
inputs = {"offered": Field()}
module, wires = named_module(state, inputs, lambda s, i: {"value": i["offered"]})
protocol = ProtocolModule(
    "register", "1", module, wires, state, inputs, ("value",),
    (PropertySpec("stores_input", op("eq", ref("value", "next"),
                                   ref("offered", "input")), "step"),),
)
result = check(protocol, backend="both", directory="evidence", depth=16, timeout=30)
```

Callbacks run once during circuit construction. State updates omitted from the
returned mapping hold their previous value. Scalar Int and Bool operations use
the existing LIA expression/term constructors; symbolic truth-testing in Python
is rejected. `protocol_layout` supplies finite maps with presence flags,
membership sets, insertion-ordered counters, and finite selectors. Their Python
loops create wires; no runtime container implementation sits outside RM.

Alternatively supply an existing discrete `zrth.Module`, including composition
and hiding, with named bindings. The exporter reads actual atom initialization
and update blocks in dependency order. It supports current controlled/input
wires and next controlled wires produced by preceding atoms. Next external
inputs, missing initialization, unsupported theories/operators, scalar-sort
mismatches, aliased bindings, and nonzero continuous dynamics are rejected.
Unused contract inputs are permitted and remain explicitly declared.

An input domain restricts allowed actions. A state domain is a premise for
one-step proof obligations only: bounded reachability never silently discards an
out-of-range successor. Overflow behavior belongs in the authored RM model.
Assumption descriptions are documentation, not magic solver constraints: any
semantic restriction must occur in the input domain, transition, or formula.

## Statements and evidence

The JSON formula language has named `state`, `input`, and `next` references,
integer/Boolean literals, LIA binary operators, `not`, and `ite`. One formula
produces both the Z3 query and the Lean obligation. Invariant/reachability/temporal
formulas use state fields only; step formulas can use all three reference phases.

- Invariant: every state reachable from initialization through allowed inputs
  satisfies the formula.
- Step: every declared-domain state/input pair satisfies the relation with its
  actual RM successor. This is stronger than checking reachable steps alone.
- Reachability: some reachable state satisfies the formula.
- Leads-to: on every infinite execution, each trigger occurrence has a later
  (possibly same-state) goal occurrence. No fairness is implicit.

Z3 performs initialization/BMC checks and separate induction/preservation
queries. Its results are always solver-only: `solver-unsat` does not become a
Lean theorem, `unknown` does not become success, and bounded absence of a
counterexample is not a proof. An induction counterexample may be unreachable.

Lean defines `Model.start`, `Model.step`, `Reachable`, `Invariant`,
`StepProperty`, and `LeadsTo` in `ReactiveModules/Protocol.lean`, and exposes a
CSLib LTS. `flatten_correct` proves flattened graph execution agrees with the
ordered atom blocks. This covers both initialization and update, not just an
instruction dispatcher. Supplied numerical wire certificates are checked by
`checkedRun_correct`; dependency bounds and every equation are verified in the
kernel. No `native_decide`, SMT axiom, or general SMT-proof replay is used.

Proof snippets can bind `proof` and `theorem` in a PropertySpec. The runner checks
`example : ProtocolArtifact.obligationN := suppliedTheorem`, not just its name.
Snippets cannot import another artifact or use admissions; axiom auditing allows
only `propext`, `Classical.choice`, and `Quot.sound`. The register example has a
universal authored proof. Solver counterexamples and authored finite/idle-lasso
witnesses can establish `lean-refuted` (or `lean-proved` for reachability).

Each evidence directory contains the full ordered-interface artifact, generated
Lean obligations, proof logs, and separate property statuses. Artifacts bind
formulas, profiles, source/proof hashes, and verification-tool hashes. A stale
or failed check never inherits an old success status. Digests are tamper/staleness
checks, **not** source-equivalence proofs or cryptographic attestations.

## Trust and limits

The host symbolic builder and Rust/Python graph export remain trusted. Kernel
proofs concern the serialized mathematical-integer RM model; they do not prove
the exporter correct, establish PyTorch fixed-width execution equivalence, or
verify CPython, TCP, operating-system scheduling, or arbitrary Python awaits.
Composition checks RM wiring, not automatic assume-guarantee compatibility.
Positive temporal solver analysis is unsupported; positive liveness needs an
authored proof with explicit fairness semantics. See the project's Paxos profile
for its additional, deliberately finite assumptions.

Tests: `python -m pytest python/tests/test_protocol.py`. The reusable nonnegative
register is `verification/examples/protocol_register.py`, with its proof under
`verification/proofs/protocol_register.lean`.
