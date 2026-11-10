"""Check that native metadata lookup propagates an actual key-allocation failure."""
# §AR-host-boundary.primitives: Allocation failure is an SDK outcome, not missing metadata.
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
    outcome = native.Outcome("manual", "bundle", "run", "incomplete", None, 1, "unavailable")
    assert outcome.observation is None
    allocation_error = False
    try:
        _testcapi.set_nomemory(0, 1)
        try:
            outcome.observation
        except MemoryError:
            allocation_error = True
    finally:
        _testcapi.remove_mem_hooks()
    assert allocation_error, "metadata lookup swallowed the real key-allocation error"
    assert outcome.observation is None
    return {
        "schema": "leancage-host-observation-allocation-v1",
        "kind": "manual native Outcome only; no engine or VM",
        "key_allocation_failure_propagated": True,
        "genuine_missing_metadata_none": True,
        "usable_after_failure": True,
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
    print("native observation: key allocation errors propagate; missing metadata remains None")


if __name__ == "__main__":
    main()
