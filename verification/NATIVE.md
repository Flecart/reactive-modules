# Native object and async source

`zrth.verified_native.compile_native` accepts ordinary function/method bodies
with native dictionary/set syntax, nested container references, Counter,
mutable instance fields, and async control flow. It is a reusable frontend:
there are no consensus-protocol names, handlers, or source hashes in its lowering.

The unchanged Paxos learning implementation is a compatibility fixture in its
own repository. It no longer requires a handwritten generator **for this
compiler path**. Its older bounded model and property proofs remain separate.

## Compile and check

```python
from zrth.verified_native import compile_native
from zrth.native_runtime import Object

bundle = compile_native("library.py", {
    "interfaces": {"Port": {"async_methods": ["send"]}}
})
bundle.certify("/tmp/native-library")
task = bundle.task("step", Object("Port"))
pending = task.run()
# The driver implements the declared external service, then resumes this token.
result = task.resume(pending, value=None)
```

```sh
uv run python -m zrth.verified_native library.py \
  --config interfaces.json --out /tmp/native-library
```

The unified CLI accepts the equivalent `python -m zrth.verified --native ...`;
native mode compiles every function/method and needs no `--entrypoint` list.

`--proof contracts.lean --theorem Library.property` checks an explicitly authored
Lean theorem against the exact compiled artifact. Omitting this checks translation,
not algorithm correctness. A source exception is a modeled failure, not a reason
to repair the source or silently substitute a value.

`bundle.construct("Actor", port)` executes the compiled constructor;
`bundle.task("Actor.step", actor, argument)` runs a method. A caller may interleave
tasks at their external suspension points. Calling `run(fuel=N)` can pause a long
computation; fuel exhaustion returns no terminal result and is never called
success. This execution budget is not a compiler or proof bound.

## Supported constructs

- Plain classes and synchronous/asynchronous functions, positional parameters,
  same-module calls with positional/keyword arguments, method calls, constructor
  state, and annotations including `Any` and unions. Annotations do not invent
  runtime type checks that Python does not perform.
- Native dictionary, set, list, and tuple literals; empty `dict()`, `set()`, and
  `Counter()`; dictionary indexing, assignment, deletion, `get`, copy and clear;
  set add/discard/remove/copy/clear; list indexing/assignment/append/copy/clear.
- Nested references and aliases, Boolean/integer key equality, dictionary
  insertion order, missing-key errors distinct from zero, Counter missing-zero
  lookup, increment, and stable insertion-order ties in `most_common(n)`.
- Local and instance-field rebinding, chained/unpacked assignments, augmented
  assignment with one evaluation of the target, numeric arithmetic and floor
  division, truthiness, chained comparisons and Boolean short-circuiting.
- Branches, early returns, while/for loops, break/continue/loop-else, and awaits
  inside branches, loops, expression operands, and nested async helper calls.
  An async call creates a suspended call value; awaiting it creates its frame.
- Explicit raises and propagation of modeled errors through nested frames.
  The adapter for `backoff.on_exception(backoff.expo, E, max_tries=N)` preserves
  changes made before failure, retries with fresh locals, and propagates exhausted
  errors to callers. Retry delays remain explicit external suspensions.
- Print and f-string diagnostics used by the compatibility fixture are observed.
  Unicode quoting uses checked-in CPython Unicode 15.1 data. That data and its
  correspondence to CPython are a declared trust boundary, not a proved Unicode
  standard implementation.

The value profile uses mathematical integers, Booleans, null, Unicode scalar
strings, and finite acyclic container/record graphs. Aliases are allowed; cycles,
floats, unpaired surrogates, arbitrary hashable host objects, user-defined Python
data-model methods, arbitrary imports/calls, reflection, and coroutine-object
identity/reuse/formatting are not covered. Coroutine call values must be awaited
at most once; that dynamic restriction is a profile assumption, not a static
linearity proof. `is`/`is not` require a right-hand
`None`/`True`/`False`; CPython scalar interning is not modeled.

This is not all of Python or asyncio. Comprehensions, general try/except/finally,
context managers, generators, task creation/cancellation, native set iteration,
live dictionary views, and custom format specifications are not supported.
Mutation while iterating a dictionary and cyclic graphs constructed during an
execution are outside this profile. Only the listed builtin/container method
forms are modeled; arbitrary runtime dispatch is not an escape hatch into host
Python. Pure helpers and async helpers can use the same supported constructs.

## What RM and Lean do

```text
unchanged Python bytes
  → trusted AST/name/schema/control-flow elaboration
  → source instruction tape + literals + functions + interfaces
  → actual RM instruction-selection graphs
  → Lean-checked selection and object/async-machine execution
```

This backend is an **RM-controlled object machine**, not a native Rust/PyTorch
dictionary tensor. RM selects the next primitive instruction. The reusable
`ReactiveModules.Objects` and `ReactiveModules.Native` definitions give those
instructions their heap, value, control-flow, call-stack, exception, retry, and
suspension semantics. There is no arbitrary Python callback or assumed segment
equality standing in for these internal operations in the Lean model.

The instruction selector is partitioned into pages for certificate size. Page
size bounds neither dictionaries nor counters, integers, call depth, loop
iterations, nor execution length. Lean proves page composition as well as each
actual exported RM graph's certificate.

Generated `native_fetch_correct`, `native_step_correct`, and
`native_execution_correct` connect the compiled graphs to the source instruction
model for every state and finite action sequence. The last theorem includes
all branches, call stacks, heap/error states, and external replies in that model;
it is not merely a successful-run trace check.

**AST-to-instruction elaboration remains trusted**, including Python evaluation
order and its correspondence to this source subset. This is a larger frontend
than the immutable-handler parser, not a mechanized CPython compiler proof.
The native RM serialization boundary and mathematical-integer interpreter remain
as documented in README.md. Native Rust/tensor execution is not certified here.

## External interfaces and evidence

Interface configuration binds imported names to records, exception types, or
external objects with declared async methods. Transport calls become requests;
the environment chooses when to return a value or raise a declared exception.
Socket internals, message-copy/delivery guarantees, the real event loop, module
initialization, OS I/O, logging infrastructure, and wall-clock timing are outside
the compiler theorem. Safety/liveness contracts must state the required adapter
and fairness assumptions. The retry model includes no wall-clock guarantee.

The reference runtime uses native Python containers but does not execute source
modules or arbitrary host calls. `native_checks.Recorder` captures primitive
instruction and external-reply samples and replays them in Lean, including the instruction selected
at the recorded program counter, heap references, frames, errors, requests and
printed output. Set storage order is intentionally not an observation. These
are **sampled runtime/model comparisons**, separately labeled from universal
compiled/source-machine equivalence. They are not a universal proof of the
Python runtime adapter. The learning repository also compares against the real,
unchanged Python coroutines at each suspension and return/failure boundary.

Evidence includes source/tool hashes, instructions and source locations, schemas,
interfaces and retry policies, actual RM terms, Lean certificates, named property
results, runtime samples, and axiom audits. Failed checks clear their corresponding
success status. Kernel replay uses `decide +kernel`, not `native_decide`;
audits reject `sorryAx` and nonstandard correctness axioms.

## Writing properties

Import `Certificate` and use `Verified.native_program`, `Verified.native_fetch`,
`Native.State`, `Native.step`, and `Native.run`. A state includes the heap, saved
frames, current phase, and observations. `Objects.lookup` and `Objects.object`
let contracts describe source-named fields rather than generated scalar offsets.

`Native.Action.tick` performs an internal machine step; `Native.Action.reply`
supplies a result at an external suspension. A complete protocol specification
must also define its network/environment composition and admissible scheduling.
No fairness or algorithm-correctness assumptions are inserted by compilation.
The older register/channel contracts remain useful examples of explicit safety,
liveness, and negative-property checks.

`proofs/native_async.lean` is a small native-backend example: it states that the
compiled `increment` async helper returns `value + 1` for **every** integer
argument, and proves the statement by transporting through the generated
execution theorem and reducing the source-machine steps. The saved
`verification/check.py` runner checks this named contract separately from the
sampled whole-function container/await checks. This helper contract is not a
correctness claim about an arbitrary caller or protocol.
