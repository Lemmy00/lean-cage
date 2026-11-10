"""Exercise the actual native GC visitor on owned manual Outcome cycles."""
# §AR-host-boundary.interfaces.gateway: SDK traversal calls the maintained native body.
import argparse
import gc
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import weakref


def run(extension):
    spec = importlib.util.spec_from_file_location("_host", extension)
    native = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)

    class Marker:
        pass

    def cycle(index):
        outcome = native.Outcome(str(index), "bundle", "run", "complete", None, 0, "fixture")
        marker = Marker()
        marker.outcome = outcome
        outcome.error = marker
        assert outcome.error is marker
        assert gc.is_tracked(outcome)
        return weakref.ref(marker)

    enabled = gc.isenabled()
    try:
        gc.disable()
        references = [cycle(index) for index in range(64)]
        assert all(reference() is not None for reference in references)
        collected = gc.collect()
        assert all(reference() is None for reference in references), "native cycle was not traversed and released"
    finally:
        if enabled:
            gc.enable()

    later = native.Outcome("later", "bundle", "run", "complete", None, 0, "fixture")
    assert later.request_id == "later" and later.observation is None
    return {
        "schema": "leancage-host-gc-visitor-v1",
        "scope": "owned manual Outcome cycles; no engine or VM",
        "cycles": len(references),
        "live_before_collection": True,
        "all_released": True,
        "collected_objects": collected,
        "later_constructor_usable": True,
        "interpreter": sys.version,
        "extension_sha256": hashlib.sha256(extension.read_bytes()).hexdigest(),
        "fixture_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--extension", type=Path, required=True)
    parser.add_argument("--record", type=Path)
    arguments = parser.parse_args()
    result = run(arguments.extension.resolve())
    if arguments.record:
        arguments.record.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("native GC: 64 owned Outcome cycles traversed and released; later construction usable")


if __name__ == "__main__":
    main()
