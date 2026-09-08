# Checked Python libraries

The first supported-subset release compiles ordinary typed Python handlers into
actual RM update graphs and checks translation certificates and library contracts
in Lean. There is no per-algorithm source generator. The permissive analyzer is
unchanged; the new API is `zrth.verified`.

## Run

From this checkout, with uv, Rust, just, and elan installed:

```sh
just py-build
cd verification/lean
lake exe cache get
lake build
cd ../..
uv run python verification/check.py
```

The final command rebuilds examples, checks proofs and negative cases, runs saved
tests, and writes `verification/bundles/results.json`. `--skip-tests` skips only
pytest. Dedicated verification CI requires Lean; ordinary Python-only tests skip
certificate checks when Lean is absent.

For a new library:

```sh
uv run python -m zrth.verified library.py --entrypoint step --out /tmp/library-evidence
```

Add `--proof contracts.lean --theorem MyLibrary.property` for each authored
property. Checking translation alone does **not** certify algorithm correctness.

```python
from zrth.verified import compile_module

bundle = compile_module("library.py", ["step"], {"assumptions": "documented profile"})
bundle.certify("/tmp/library-evidence")
bundle.check_properties("/tmp/library-evidence", "contracts.lean", ["MyLibrary.property"])
```

`bundle.modules` contains real `zrth.Module` objects. `bundle.run` interprets
their exported update graphs with mathematical integers for differential tests.
Configuration records assumptions; it cannot insert code or assumed theorems.

## Supported source interface

Use frozen dataclasses for state, messages, and effects, with annotated functions
returning new state and effect records. A driver passes returned state into the
next invocation and executes communication requests outside the handler.

- Types: exact Python `int`/`bool`, distinct integer-valued enums, nested frozen
  records, fixed tuples, and optional values. Optional record access requires
  an explicit `is not None` branch.
- Statements: local/record rebinding, branches, early returns, and pass.
  Every entrypoint path must return. Record assignments evaluate all right-hand
  sides before rebinding any fields.
- Expressions: Boolean operations, comparisons, addition/subtraction, conditional
  expressions, and record construction. Numeric truthiness is rejected.
- Records have explicit fields without defaults, inheritance, methods, special
  fields, or custom decorators. Parameter values must satisfy declared schemas.

Mutable collections, loops, helper calls, dynamic dispatch, exceptions, async,
and arbitrary imports/effects are rejected—not silently abstracted. The RM
adapter currently accepts literal operands representable in signed 64 bits,
but variable values and arithmetic are unbounded mathematical integers.
Tensor execution and its overflow behavior are not the certified semantics.

## Checked connection and trust boundary

```text
Python bytes → trusted parser/schema resolution/fixed record layout → source AST
  → untrusted candidate emitter → actual RM update graph
  → Lean type/initialization checks and comparison to a proved canonical lowering
  → explicitly authored library and composition proofs
```

`Source.lower_correct` proves the generic lowering. `Graph.source_correct`
connects wire execution to the source-style representation of that graph.
`certified_correct` connects each checked RM graph to its source AST. The final
graph is checked, not just its hash or the candidate compiler's output label.

**The parser/schema elaborator and correspondence between this declared subset
and the Python runtime remain trusted.** This is not a mechanized proof of
CPython, its parser, dataclasses, the OS, or a socket adapter. The compiler never
imports source modules, and certification rebinds the AST to freshly parsed
source. Hashes identify artifacts; they are not semantic proofs.

Only exported handler update blocks are certified here. Arbitrary RM
initialization/composition and differential/tensor theories are not covered.
The channel explicitly invokes compiled initial handlers and proves its network
adapter agrees with the actual compiled sender and receiver graphs.

Proofs use ordinary Lean checking, not `native_decide` or unchecked SMT verdicts.
Audits allow only `propext`, `Quot.sound`, and `Classical.choice`. No `sorry` or
algorithm-correctness axioms support the advertised results. Specifications must
still be reviewed: compilation cannot infer the author's intention.

## Library guarantees

| Example | Checked result |
| --- | --- |
| Register | Result is at least the previous and offered values, and is one of them, for every integer input. |
| Channel safety | Received values form a prefix of accepted values; request IDs are delivered at most once; completion never precedes delivery. |
| Channel liveness | Every pending/accepted request completes under infinitely-often ticks and fair loss in both directions. |
| Non-vacuity | An actual request is accepted, delivered, and acknowledged, followed by an infinite fair execution. |
| Incorrect register | Translation checks, the positive proof fails, and Lean proves a refutation of monotonicity. |

The channel permits loss, duplication and reordering of genuine queued packets.
Handlers run serially to completion. A busy sender rejects new submissions;
liveness covers **accepted** requests. There are no sequence-number/history
bounds, no crash/restart or forged-message claims, and no wall-clock guarantee.
Fair loss concerns infinitely repeated transmissions, not guaranteed success of
each packet. Safety needs no fairness assumption.

CSLib supplies reachability and infinite executions. Reusable fault semantics,
packet-predicate preservation, and fair-loss definitions are in
`ReactiveModules.Network`; protocol-specific invariants belong in library proofs.

## Evidence and next stages

Bundles contain source, schemas, RM terms, tool-source hashes, Lean version,
certificates, named theorem results, and axiom audits. Lean/CSLib/transitive
revisions are pinned in the Lake manifest. Failed rechecks clear relevant success
statuses. Source, tooling, and certificate changes require recertification.
These records are not signed security attestations.

Generic mutable-container semantics and async continuations are next. Existing
async/container-heavy code is not accepted unchanged yet. The Paxos learning
implementation therefore retains its legacy generator until those stages pass.
