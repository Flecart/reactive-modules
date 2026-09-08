"""Check unbounded heap/interface model proofs and sampled Python/Lean traces.

This explicitly does NOT claim checked Python container/async compilation.
"""
import hashlib
import json
from pathlib import Path
import random
import subprocess

import zrth.effects as effects
from zrth.effects import Heap, Operation as Op, Request
from zrth.verified_backend import audit_axioms, provenance

ROOT = Path(__file__).resolve().parent
OPERATIONS = dict(zip(Op, (
    "newDict", "newSet", "dictSet", "dictGet", "dictContains", "dictLen", "dictDelete",
    "dictCopy", "dictKeyAt", "setAdd", "setDiscard", "setContains", "setLen", "setRemove",
    "setCopy", "dictItem", "dictClear", "setClear"), strict=True))
THEOREMS = [
    "Heap.lookup_put_same", "Heap.lookup_put_other", "Heap.lookup_erase_same",
    "Heap.overwrite_keeps_order", "Heap.put_preserves_unique_keys",
    "Heap.mem_setAdd", "Heap.setAdd_idempotent", "Heap.mem_setErase", "Heap.setAdd_preserves_unique",
    "Heap.error_preserves_heap", "Heap.allocate_fresh", "Heap.allocate_preserves",
    "Heap.replace_preserves_other", "Effects.stale_has_no_effect", "Effects.foreign_has_no_effect",
    "Effects.resume_advances_epoch", "Effects.replay_has_no_effect", "Effects.serve_congr",
]


def source_hashes():
    hashes = provenance()
    for path in [Path(effects.__file__).resolve(), Path(__file__).resolve()]:
        hashes[str(path.relative_to(ROOT.parent))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return hashes


def integer(n):
    if type(n) is not int:
        raise TypeError("expected exact integer")
    return f"({n})"


def lean_request(request):
    return f"⟨.{OPERATIONS[request.operation]}, {integer(request.reference)}, {integer(request.key)}, {integer(request.value)}⟩"


def lean_response(response):
    if response.error is None:
        return f".ok {integer(response.value)}"
    return f".error (.{response.error} {integer(response.detail)})"


def lean_store(snapshot):
    objects = []
    for kind, values in snapshot:
        if kind == "dict":
            entries = ", ".join(f"({integer(k)}, {integer(v)})" for k, v in values)
            objects.append(f".dictionary [{entries}]")
        else:
            entries = ", ".join(integer(k) for k in sorted(values))
            objects.append(f".set [{entries}]")
    return "[" + ", ".join(objects) + "]"


def traces():
    # Cover every operation, insertion order, negative indices, copies, errors,
    # and integers beyond native machine width. The random traces add mixtures.
    targeted = [Request(Op.NEW_DICT), Request(Op.NEW_SET),
                Request(Op.DICT_SET, 0, 2**100, -(2**120)), Request(Op.DICT_SET, 0, -9, 0),
                Request(Op.DICT_SET, 0, 2**100, 8), Request(Op.DICT_COPY, 0),
                Request(Op.DICT_DELETE, 0, 2**100), Request(Op.DICT_SET, 0, 2**100, 7),
                Request(Op.DICT_KEY_AT, 0, -1), Request(Op.DICT_KEY_AT, 0, -(2**100)),
                Request(Op.DICT_KEY_AT, 0, 2**100), Request(Op.DICT_ITEM, 2, 2**100),
                Request(Op.DICT_GET, 0, 77, -123), Request(Op.DICT_CONTAINS, 0, -9),
                Request(Op.DICT_LEN, 0), Request(Op.DICT_ITEM, 0, 77),
                Request(Op.DICT_DELETE, 0, 77), Request(Op.SET_ADD, 1, 3),
                Request(Op.SET_ADD, 1, 3), Request(Op.SET_ADD, 1, -8), Request(Op.SET_COPY, 1),
                Request(Op.SET_DISCARD, 1, 77), Request(Op.SET_CONTAINS, 1, 3),
                Request(Op.SET_LEN, 1), Request(Op.SET_REMOVE, 1, 3), Request(Op.SET_REMOVE, 1, 3),
                Request(Op.SET_CLEAR, 1), Request(Op.DICT_CLEAR, 0),
                Request(Op.DICT_SET, 1), Request(Op.SET_ADD, 0), Request(Op.DICT_LEN, -1),
                Request(Op.SET_LEN, 2**100)]
    assert set(r.operation for r in targeted) == set(Op)
    yield targeted
    for seed in range(8):
        rng = random.Random(seed)
        yield [Request(Op.NEW_DICT), Request(Op.NEW_SET)] + [
            Request(rng.choice(list(Op)), rng.randrange(-1, 6), rng.randrange(-3, 4), rng.randrange(-9, 10))
            for _ in range(28)]


def main():
    output = ROOT / "bundles/effects"
    output.mkdir(parents=True, exist_ok=True)
    status_path = output / "status.json"
    status_path.write_text(json.dumps({"model_checks": "not-established",
                                      "container_lowering": "not-established", "async_lowering": "not-established"}) + "\n")
    hashes = source_hashes()
    source = ["import ReactiveModules", "open ReactiveModules", "namespace EffectChecks",
              "set_option maxRecDepth 100000", "set_option maxHeartbeats 20000000", '''
def sameObject : Heap.Object → Heap.Object → Bool
  | .dictionary a, .dictionary b => decide (a = b)
  | .set a, .set b => a.length == b.length && a.all b.contains && b.all a.contains
  | _, _ => false

def sameStore : Heap.Store → Heap.Store → Bool
  | [], [] => true
  | a :: restA, b :: restB => sameObject a b && sameStore restA restB
  | _, _ => false

def checkTrace (heap : Heap.Store) (steps : List (Heap.Request × Heap.Response × Heap.Store)) : Bool :=
  match steps with
  | [] => true
  | (request, expected, snapshot) :: rest =>
    let (after, response) := Heap.apply heap request
    decide (response = expected) && sameStore after snapshot && checkTrace after rest
termination_by structural steps
''']
    transcript, count = [], 0
    for index, requests in enumerate(traces()):
        heap, rows, records = Heap(), [], []
        for request in requests:
            response = heap.apply(request)
            snapshot = heap.snapshot()
            rows.append(f"({lean_request(request)}, {lean_response(response)}, {lean_store(snapshot)})")
            records.append(dict(request=[request.operation.name, request.reference, request.key, request.value],
                                response=[response.error, response.value, response.detail],
                                snapshot=[(kind, sorted(values) if kind == "set" else values) for kind, values in snapshot]))
        source.append(f"theorem trace_{index} : checkTrace [] [{', '.join(rows)}] = true := by decide")
        source.append(f"#print axioms trace_{index}")
        transcript.append(records)
        count += len(requests)
    for theorem in THEOREMS:
        source += [f"#check {theorem}", f"#print axioms {theorem}"]
    source.append("end EffectChecks\n")
    (output / "Checks.lean").write_text("\n".join(source))
    (output / "traces.json").write_text(json.dumps(transcript, indent=2) + "\n")
    artifacts = {str(path.relative_to(ROOT.parent)): hashlib.sha256(path.read_bytes()).hexdigest()
                 for path in [output / "Checks.lean", output / "traces.json"]}
    project = ROOT / "lean"
    subprocess.run(["lake", "build"], cwd=project, check=True)
    result = subprocess.run(["lake", "env", "lean", str(output / "Checks.lean")], cwd=project,
                            text=True, capture_output=True)
    log = result.stdout + result.stderr
    (output / "audit.log").write_text(log)
    if result.returncode:
        raise ValueError(f"Lean rejected heap/interface checks; see {output / 'audit.log'}\n" + log[:3000])
    audit_axioms(log)
    if hashes != source_hashes() or any(hashlib.sha256((ROOT.parent / path).read_bytes()).hexdigest() != digest
                                      for path, digest in artifacts.items()):
        raise ValueError("effect verification sources changed during checking; rerun")
    hashes.update(artifacts)
    version = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=project, text=True).strip()
    status_path.write_text(json.dumps(dict(
        model_checks="checked", model_theorems=THEOREMS, sampled_requests=count,
        python_model_correspondence="differential-tests-only", container_lowering="not-established",
        async_lowering="not-established", sources=hashes, lean_version=version, audit="audit.log"), indent=2) + "\n")
    print(f"Heap/effect foundation: {len(THEOREMS)} model theorems and {count} sampled requests checked; no container/async lowering claim.", flush=True)


if __name__ == "__main__":
    main()
