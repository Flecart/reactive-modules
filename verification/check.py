"""Rebuild the first-release libraries, check their proofs, and run regressions."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from zrth.verified import compile_coroutine, compile_module, compile_native
from zrth.native_checks import Recorder
from zrth.native_runtime import Finished

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-tests", action="store_true")
    args = parser.parse_args()
    summary = ROOT / "bundles/results.json"
    summary.parent.mkdir(parents=True, exist_ok=True)
    summary.write_text(json.dumps({"run": "not-established"}) + "\n")
    if not args.skip_tests:
        subprocess.run([sys.executable, "-m", "pytest", "-q",
                        str(ROOT.parent / "python/tests/test_verified.py"),
                        str(ROOT.parent / "python/tests/test_verified_control_flow.py"),
                        str(ROOT.parent / "python/tests/test_effects.py"),
                        str(ROOT.parent / "python/tests/test_verified_async.py"),
                        str(ROOT.parent / "python/tests/test_verified_native.py")], check=True)
    suites = {
        "register": (["initial", "step"], ["Register.never_decreases", "Register.covers_offer", "Register.returns_an_input"]),
        "fold_register": (["step"], ["FoldRegister.never_decreases", "FoldRegister.covers_offers"]),
        "channel": (["initial_sender", "initial_receiver", "sender", "receiver"],
                    ["Channel.compiled_safety", "Channel.compiled_liveness", "Channel.nonvacuous",
                     "Channel.delivery_once", "Channel.accepted_liveness"]),
        "register_bad": (["step"], ["RegisterBug.monotonicity_refuted"]),
    }
    report = {}
    for name, (entrypoints, theorems) in suites.items():
        model = dict(integer_semantics="mathematical", source_subset="immutable-event-handlers-v2")
        if name == "channel":
            model.update(network="loss-duplication-reordering-no-forgery-no-crashes",
                         progress="infinitely-often-ticks-and-fair-loss-in-both-directions",
                         bounds="no-finite-state-or-history-bound")
        bundle = compile_module(ROOT / "examples" / (name + ".py"), entrypoints, model)
        output = ROOT / "bundles" / name
        bundle.certify(output)
        if name == "register_bad":
            try:
                bundle.check_properties(output, ROOT / "proofs/register.lean", ["Register.never_decreases"])
            except ValueError as exc:
                if "Lean did not establish" not in str(exc): raise
                (output / "rejected_positive_proof.log").write_text(str(exc) + "\n")
            else:
                raise AssertionError("incorrect register satisfied the positive proof")
        status = bundle.check_properties(output, ROOT / "proofs" / (name + ".lean"), theorems)
        report[name] = dict(result="refuted" if name == "register_bad" else "proved",
                            source_sha256=bundle.artifact["source_sha256"],
                            evidence=str(output / "status.json"), properties=status["properties"])
        print(f"{name}: {report[name]['result']}; translation and {len(theorems)} theorem(s) checked", flush=True)
    bundle = compile_coroutine(ROOT / "examples/compiled_async.py", "step",
        dict(integer_semantics="mathematical", source_subset="top-level-request-coroutines-v1",
             heap="unbounded-integer-dictionaries-and-sets", progress="three-served-requests"))
    output = ROOT / "bundles/compiled_async"
    bundle.certify(output)
    status = bundle.check_properties(output, ROOT / "proofs/compiled_async.lean", ["AsyncDictionary.round_trip"])
    report["compiled_async"] = dict(result="proved", source_sha256=bundle.artifact["source_sha256"],
        evidence=str(output / "status.json"), properties=status["properties"],
        request_coroutine_lowering="checked", native_container_syntax="unsupported")
    print("compiled_async: proved; RM segments, heap/resumption composition, and round-trip checked", flush=True)
    bundle = compile_native(ROOT / "examples/native_async.py")
    output = ROOT / "bundles/native_async"
    bundle.certify(output)
    status = bundle.check_properties(output, ROOT / "proofs/native_async.lean", ["NativeAsync.increment_result"])
    recorder = Recorder(per_signature=1)
    for limit in (0, 1, 4):
        task = recorder.attach(bundle.task("step", limit))
        assert task.run() == Finished(({i: i + 1 for i in range(limit)}, limit, limit))
    recorder.check(bundle, output)
    report["native_async"] = dict(result="translation-checked",
        source_sha256=bundle.artifact["source_sha256"],
        evidence=str(output / "status.json"),
        runtime_evidence=str(output / "runtime-status.json"),
        runtime_samples=len(recorder.samples), properties=status["properties"],
        whole_step_correctness="not-asserted")
    print("native_async: translation and helper contract checked; native containers and nested awaits kernel-replayed", flush=True)
    subprocess.run([sys.executable, str(ROOT / "check_effects.py")], check=True)
    foundation = json.loads((ROOT / "bundles/effects/status.json").read_text())
    report["effects_foundation"] = dict(result=foundation["model_checks"],
        evidence=str(ROOT / "bundles/effects/status.json"),
        container_lowering=foundation["container_lowering"], async_lowering=foundation["async_lowering"])
    summary.write_text(json.dumps(report, indent=2) + "\n")
    print("Checked-library checks passed. Native/async translation evidence is separate from algorithm-property proofs.", flush=True)


if __name__ == "__main__":
    main()
