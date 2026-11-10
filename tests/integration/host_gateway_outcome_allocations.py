"""Exercise actual native presentation under bounded, one-shot allocation failures."""
# §AR-host-boundary.primitives: A failed lookup cannot become a null runtime argument.
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


def run(extension):
    import _testcapi

    spec = importlib.util.spec_from_file_location("_host", extension)
    native = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)
    outcome = native.Outcome("allocation-fixture", "bundle", "run", "complete", None,
                             0, "fixture", stdout=b"stdout", stderr=b"stderr",
                             files={"file": b"contents"}, output=None,
                             publication="fixture")
    render = outcome.json
    expected = render()
    failures = []
    successes = 0
    for allocation in range(64):
        error = None
        result = None
        try:
            _testcapi.set_nomemory(allocation, allocation + 1)
            try:
                result = render()
            except (MemoryError, ValueError) as observed:
                error = type(observed)
        finally:
            _testcapi.remove_mem_hooks()
        if error is not None:
            failures.append({"allocation": allocation, "error": error.__name__})
        else:
            assert result == expected
            successes += 1
        assert render() == expected, "one failed call damaged the next native presentation"
        assert outcome.request_id == "allocation-fixture"
    assert failures, "the allocation fault window was not exercised"
    assert any(item["error"] == "ValueError" for item in failures), (
        "the suppressed dictionary-key allocation failure was not exercised")
    return {
        "schema": "leancage-host-outcome-allocation-v1",
        "scope": "manual native Outcome and hashes only; no engine or VM",
        "allocation_windows": 64,
        "failures": failures,
        "successful_windows": successes,
        "usable_after_every_failure": True,
        "interpreter": sys.version,
        "extension_sha256": hashlib.sha256(extension.read_bytes()).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--extension", type=Path, required=True)
    parser.add_argument("--record", type=Path)
    arguments = parser.parse_args()
    result = run(arguments.extension.resolve())
    if arguments.record:
        arguments.record.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("native Outcome: 64 allocation windows preserve explicit errors and later use")


if __name__ == "__main__":
    main()
