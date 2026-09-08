"""Rebuild the first-release libraries, check their proofs, and run regressions."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from zrth.verified import compile_module

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-tests", action="store_true")
    args = parser.parse_args()
    if not args.skip_tests:
        subprocess.run([sys.executable, "-m", "pytest", "-q", str(ROOT.parent / "python/tests/test_verified.py")], check=True)
    suites = {
        "register": (["initial", "step"], ["Register.never_decreases", "Register.covers_offer", "Register.returns_an_input"]),
        "channel": (["initial_sender", "initial_receiver", "sender", "receiver"],
                    ["Channel.compiled_safety", "Channel.compiled_liveness", "Channel.nonvacuous",
                     "Channel.delivery_once", "Channel.accepted_liveness"]),
        "register_bad": (["step"], ["RegisterBug.monotonicity_refuted"]),
    }
    report = {}
    for name, (entrypoints, theorems) in suites.items():
        model = dict(integer_semantics="mathematical", source_subset="immutable-event-handlers-v1")
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
    (ROOT / "bundles" / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print("First-release checks passed. This does not compile async Paxos yet.", flush=True)


if __name__ == "__main__":
    main()
