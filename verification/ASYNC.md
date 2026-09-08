# Compiled Request coroutines

For native `dict`/`set` syntax, nested awaits, async helpers, and mutable classes,
use the newer [native object/async compiler](NATIVE.md). This document describes
the smaller, still-supported explicit-Request segment compiler.

`zrth.verified.compile_coroutine` connects the heap/effect interface to the
compiler. It reads Python source without importing or executing it, splits a
supported coroutine at each await, and produces actual native RM update graphs
for the segments. No algorithm-specific generator is involved.

```python
from zrth.effects import Operation as Op, Request

async def step(key: int, value: int) -> int:
    reference = await Request(Op.NEW_DICT)
    await Request(Op.DICT_SET, reference, key, value)
    result = await Request(Op.DICT_ITEM, reference, key)
    return result
```

This example produces four graphs: before allocation, before insertion, before
lookup, and after lookup. Each suspension returns a request plus a flattened
local frame; resumption supplies that frame and the integer service response
to the next graph. Exceptions become a failed task, not a made-up integer.
The heap remains an explicit unbounded service, not a native scalar/tensor wire.

## Run

From an installed upstream checkout:

```sh
uv run python -m zrth.verified verification/examples/compiled_async.py \
  --coroutine --entrypoint step --out /tmp/compiled-async \
  --proof verification/proofs/compiled_async.lean \
  --theorem AsyncDictionary.round_trip
uv run python -m pytest -q python/tests/test_verified_async.py
```

The saved `verification/check.py` runner includes both the tests and this proof.
Its `compiled_async` report is distinct from the standalone effect foundation.

```python
from zrth.verified import compile_coroutine

bundle = compile_coroutine("verification/examples/compiled_async.py", "step")
bundle.certify("/tmp/compiled-async")
assert bundle.run(7, 99) == [99]
```

Like synchronous `bundle.run`, results are flattened scalar lists. To choose
interleavings, use `bundle.task(7, 99)`, then `start()` and `serve(pending, heap)`
from the [effect runtime](EFFECTS.md). Tasks can share a heap. Each compiled task
executes the exported RM graph snapshots using mathematical integer semantics.
Calling `run` or `task` alone does not perform certification.

## Supported subset

- Annotated `async def` with a final top-level return and exact schema-checked
  parameters. An async function with no await is also supported.
- Top-level `await Request(Op.MEMBER, ...)`, optionally assigned to one integer
  local or used as the final return. Operation must be a literal imported member;
  integer request fields may be positional or keyword arguments. Import aliases
  are supported. All 18 dictionary/set operations are available.
- Pure computation between awaits uses the existing typed handler subset:
  frozen records, fixed tuples, optional values, branches, nonrecursive pure
  helpers, and fixed-tuple loops. Helpers may have early returns.
- Locals retain their values and types across suspension, including aliases to
  integer heap references. Currently all local bindings are saved, so even a
  dead local introduced on only one branch is conservatively rejected.

Rejected: native `dict`/`set` construction, indexing or mutation; awaits in
branches, loops, or nested expressions; async helper calls; early coroutine
returns; `try`/`except`; arbitrary awaitables, imports, I/O, and asyncio APIs.
The more permissive reference `Task` runtime can execute some of these Python
constructs, but that does not make them part of the compiled subset.

## What is proved

Every generated segment has the existing source-AST/RM-graph correctness
certificate. Lean also checks the adjoining frame sorts and response slot.
`coroutine_blocks_correct` discharges the segment-equality obligation from these
certificates; it is not an assumed hypothesis of the generated final theorem.
`coroutine_segment_correct`, `coroutine_start_correct`, `coroutine_serve_correct`,
and `coroutine_execution_correct` establish equality with the declared source
coroutine model, including heap state and errors, for arbitrary finite ticket
sequences. This includes rejected stale/foreign tickets. There is no numeric or
heap-capacity cutoff.

The authored `AsyncDictionary.round_trip` theorem proves that the example's
compiled task returns the value it stored, for **all integer keys and values**,
starting with an empty heap and serving its three requests. This is a conditional
completion guarantee, not scheduler fairness or unconditional liveness. The
compiler preserves behavior; other algorithm contracts still need their own
statements and proofs. Incorrect source is not repaired.

## Trust boundary

The Python parser/schema elaborator, including recognition of await boundaries
and construction of frame layouts, remains trusted. The theorem starts at that
elaborated source-coroutine model; it is not a mechanized CPython or asyncio
semantics proof. Source bytes and control metadata are rebound during
certification; changing an operation, schema, or boundary invalidates evidence.

The native RM syntax/export interface is trusted as documented in README.md.
The theorem does not cover the native Rust/tensor interpreter. The Python heap
service and coroutine runtime adapter are differentially tested, not universally
proved implementations of Lean's model. Tests compare original Python and
compiled RM task requests, responses, heap observations, errors, and interleavings.
There is no claim about sockets, cancellation, concurrency within a segment,
crashes, persistence, garbage collection, or arbitrary host effects.

Lean checks the translation and authored proof without `native_decide`, `sorry`,
or algorithm-specific correctness axioms. Axiom audits allow only the standard
`propext`, `Quot.sound`, and `Classical.choice` dependencies.

The unchanged Paxos implementation uses the separate native compiler, not this
restricted explicit-Request entrypoint.
