# Unbounded containers and explicit async effects: foundation

This increment adds executable integer dictionary/set services and a mathematical
heap/suspension model. It does not itself establish compiler correctness.
The separate [async compiler connection](ASYNC.md) now compiles typed
`async def` handlers using top-level `await Request(...)` into RM segments and
checks composition with this model. Native Python `dict`/`set` syntax remains
unsupported by the compiler.

## Try it

From this upstream checkout, after installing/building the Python package:

```sh
uv run python verification/examples/async_containers.py
uv run python verification/check_effects.py
uv run python -m pytest -q python/tests/test_effects.py
```

The normal `verification/check.py` runner includes the new tests/model checks.
Evidence is written to `verification/bundles/effects`. Its manifest separately
labels model theorems, sampled Python/model agreement, and the still-unestablished
container and async lowering connections **for this standalone foundation
artifact**. The connected compiler has separate evidence in `bundles/compiled_async`.

## Heap interface

`zrth.effects.Heap` owns native Python dictionaries and sets, addressed by stable
integer references. It supports allocation, lookup with a default, lookup that
raises on absence, assignment, membership, length, deletion, copy, and clear.
Sets also support add/discard/remove. Dictionary key indexing exposes insertion
order, including negative indices. Overwriting retains order; deleting and
reinserting moves a key to the end. Sets do not expose an iteration order.

There is no capacity, integer-width, history, or execution-length cutoff. Keys
and values are **exact Python integers**. Booleans, strings, arbitrary hashable
objects, container-valued entries, recursive schemas, and automatic encoding of
Python object graphs are not supported yet. In particular this does not silently
treat `True` and `1` as different Python dictionary keys: Boolean keys are rejected.

Copying a reference preserves aliasing; copying an object allocates a new object.
Absent keys are distinct from values such as zero. Invalid references, wrong
object kinds, missing keys, and bad indices are explicit responses, and failed
operations leave the heap unchanged. Allocation and objects have no deallocation
or garbage-collection semantics yet.

`Request` is awaitable. For example:

```python
from zrth.effects import Heap, Operation as Op, Request, Task

async def make():
    ref = await Request(Op.NEW_DICT)
    await Request(Op.DICT_SET, ref, 7, 99)
    return await Request(Op.DICT_ITEM, ref, 7)

heap = Heap()
task = Task(make())
pending = task.start()        # yields a request; no heap operation yet
pending = task.serve(pending, heap)  # allocates, then resumes to the next await
pending = task.serve(pending, heap)  # assigns, then resumes
finished = task.serve(pending, heap) # returns Finished(99)
```

Multiple tasks may share the heap. A caller chooses their interleavings. The
runner uses real Python coroutines, so exceptions from responses reach ordinary
Python exception handlers, and nested async helpers suspend naturally. This
runtime behavior is tested, not covered by a Python compiler proof.

## Suspension boundary

Every yielded request has a single-use, identity-based `Pending` token. The task
rejects stale, foreign, and forged tokens **before** applying a heap effect.
Reentrant code cannot reuse the token being resumed. `resume` can also inject an
explicit `Response` without executing the service; correctness of an externally
supplied response is then the caller's responsibility. `serve` uses the actual
heap response. Calls to this reference runner are serial; it is not thread-safe.

This is an effect interface, not an asyncio event loop or socket adapter. Every
externally yielded object must be a `Request`. Awaitables that finish without
yielding execute inside a segment. No claim is made about arbitrary third-party
awaitables, CPython internals, cancellation, crashes, persistence, real-time
behavior, fairness, or network exactly-once delivery. `close()` is cleanup outside
the formal model. A request that never receives a response can stay suspended
forever. Regular Python I/O inside a coroutine is not sandboxed or verified.

## What Lean checks

`ReactiveModules.Heap` defines unbounded ordered dictionaries, sets, object
allocation, references, and the 18 request operations. It proves lookup/update
laws, dictionary overwrite-order preservation, uniqueness preservation for
insertion, set membership/idempotence laws, fresh allocation, preservation of
other objects, and error nonmutation. These are mathematical model theorems.

`ReactiveModules.Effects` defines ready/waiting/done/failed phases, response
continuations, task owners, and monotonically increasing suspension epochs. It
proves that stale/foreign requests cannot change state and that replay after a
served request cannot apply the effect again. Owner IDs are assumed distinct
between tasks; the Python runner uses token object identity for isolation.

The model abstracts terminating Python computation between effects as a supplied
segment function. Its `serve_congr` theorem requires equality between source and
compiled segment functions; it does not establish that equality itself. The
new compiler discharges it for its supported subset using RM segment certificates
and `ReactiveModules.Coroutine`. The Python service
and coroutine runner are not mechanically proved implementations of the model.

`check_effects.py` additionally replays saved/seeded request traces from native
Python containers in Lean, checking every response and heap observation with
ordinary kernel checking. These are finite differential checks, **not** a
universal Python-runtime equivalence proof. Axiom audits reject `sorry` and
`native_decide` dependencies. Existing register/channel proofs are rechecked too.

## Next compiler work

The checked heap-service boundary and top-level Request suspension/frame lowering
are now connected; native scalar/tensor wires still do not store a heap.

1. Elaborate native typed container operations into that interface, including allocation,
   aliasing, missing-key exceptions, and eventually nested/reference-valued schemas.
2. Extend suspension lowering to branches, loops, async helpers, and exceptions.
   An `await` must not be erased into a synchronous call.

Paxos remains on its legacy source-specific path until its constructs are covered.
