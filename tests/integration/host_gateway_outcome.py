"""Exercise Outcome presentation while ordinary callbacks reinitialize the same receiver."""
# §AR-host-boundary.interfaces.gateway: Each selected presentation dictionary has a native root.
import argparse
import gc
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import weakref


def load(path):
    spec = importlib.util.spec_from_file_location("_host", path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def run(extension):
    native = load(extension)
    observations = []

    def initialize(outcome, report=None):
        outcome.__init__("replacement", "bundle", "run", "incomplete", report,
                         1, False, stdout=b"", stderr=b"", files={})

    class Payload:
        pass

    payload = Payload()
    original = native.Outcome("original", "bundle", "run", "incomplete", payload,
                              1, False, stdout=b"", stderr=b"", files={})
    reference = weakref.ref(payload)
    del payload
    selected_json = original.json
    phase = {"armed": False, "observed": False}

    def reenter(when, information):
        del information
        if when != "start" or not phase["armed"] or phase["observed"]:
            return
        phase["observed"] = True
        phase["armed"] = False
        initialize(original)
        # The current C invocation owns the selected source dictionary independently.
        observations.append({"json_reinitialized": original.request_id == "replacement",
                             "selected_report_alive": reference() is not None})

    def call_json(call):
        phase["armed"] = True
        return call()

    thresholds = gc.get_threshold()
    enabled = gc.isenabled()
    gc.disable()
    gc.collect()
    gc.callbacks.append(reenter)
    try:
        gc.set_threshold(1, 1_000_000, 1_000_000)
        gc.enable()
        snapshot = call_json(selected_json)
    finally:
        phase["armed"] = False
        gc.callbacks.remove(reenter)
        gc.set_threshold(*thresholds)
        if not enabled:
            gc.disable()
    assert phase["observed"], "the native json allocation did not trigger the ordinary GC callback"
    assert observations == [{"json_reinitialized": True, "selected_report_alive": True}], observations
    assert snapshot["request_id"] == "original"
    assert snapshot["report"] is reference()
    assert original.request_id == "replacement"
    del snapshot, selected_json, original
    gc.collect()
    assert reference() is None

    # A replaced field can run its destructor inside PyDict_SetItemString. Reinitializing
    # the same receiver must not drop the selected dictionary or its other fields early.
    payload = Payload()
    record = native.Outcome("setter", "bundle", "run", "incomplete", payload, 1, False)
    report_reference = weakref.ref(payload)
    del payload

    class ReinitializeOnRelease:
        def __del__(self):
            initialize(record)
            observations.append({"setter_reinitialized": record.request_id == "replacement",
                                 "selected_report_alive": report_reference() is not None})

    record.error = ReinitializeOnRelease()
    record.error = None
    assert observations[-1] == {"setter_reinitialized": True, "selected_report_alive": True}
    assert record.request_id == "replacement"
    gc.collect()
    assert report_reference() is None
    del record
    return {"schema": "leancage-host-native-outcome-roots-v1", "observations": observations,
            "interpreter": sys.version, "extension_sha256": hashlib.sha256(extension.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--extension", type=Path, required=True)
    parser.add_argument("--record", type=Path)
    arguments = parser.parse_args()
    result = run(arguments.extension.resolve())
    if arguments.record:
        arguments.record.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("native Outcome roots: same-receiver json GC and setter-destructor reentry passed")


if __name__ == "__main__":
    main()
