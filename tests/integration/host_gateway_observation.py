"""Exercise actual native projection with a replaced Path factory and lossless OS bytes."""
# §AR-host-boundary.interfaces.gateway: Engine observations bypass mutable Path presentation.
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys


def run(extension):
    spec = importlib.util.spec_from_file_location("_host", extension)
    native = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)
    root = extension.parents[2]
    engine = root / "bin/leancage-host"
    expected_engine = Path(__file__).with_name("host_observation_engine.py")
    assert engine.read_bytes() == expected_engine.read_bytes(), "use the isolated projection fixture"
    workspace = native.Workspace(bundle=os.fsencode(root), results=os.fsencode(root / "runs"))
    original_new = Path.__new__
    alias = {"presentation": "mutable callback result"}
    captured = []
    replacement_rejections = []

    def replacement(cls, value):
        del cls
        captured.append(value)
        for name, changed in (("observation", property(lambda self: {})),
                              ("output", property(lambda self: {})),
                              ("__getattribute__", lambda self, name: None),
                              ("__class__", type)):
            try:
                setattr(native.Outcome, name, changed)
            except (TypeError, AttributeError):
                replacement_rejections.append(name)
            else:
                raise AssertionError("Path callback replaced the native Outcome class: " + name)
        return alias

    raw_output = os.fsencode(root) + b"/returned-\xff"
    try:
        Path.__new__ = staticmethod(replacement)
        outcome = workspace.run(b"{}", output=raw_output)
    finally:
        Path.__new__ = original_new
    expected_output = os.fsdecode(raw_output)
    assert captured == [expected_output], repr(captured)
    assert replacement_rejections == ["observation", "output", "__getattribute__", "__class__"]
    assert outcome.output is alias
    alias["presentation"] = "changed after return"
    assert outcome.json()["output"] == str(alias)
    observation = outcome.observation
    assert observation == {"schema": "native-projection-fixture", "output": expected_output,
                           "request_id": "projection-fixture"}
    assert os.fsencode(observation["output"]) == raw_output
    try:
        outcome.observation = {}
    except AttributeError:
        pass
    else:
        raise AssertionError("observation property permits reassignment")
    for changed_class in (dict, native.Outcome):
        try:
            outcome.__class__ = changed_class
        except (TypeError, AttributeError):
            pass
        else:
            raise AssertionError("Outcome instance class assignment is mutable")
    outcome.request_id = "presentation changed"
    assert outcome.request_id == "presentation changed"
    assert observation["request_id"] == "projection-fixture"
    outcome.__init__("manual", "bundle", "run", "incomplete", None, 1, "unavailable")
    assert outcome.observation is None
    assert observation["output"] == expected_output
    manual = native.Outcome("manual", "bundle", "run", "incomplete", None, 1, "unavailable")
    assert manual.observation is None
    return {"schema": "leancage-host-native-observation-v1", "kind": "projection fixture; no VM",
            "path_callback_observed": True, "raw_output_roundtrip": True,
            "manual_observation_none": True, "read_only_property": True,
            "class_replacements_rejected": replacement_rejections,
            "instance_fields_mutable": True, "interpreter": sys.version,
            "extension_sha256": hashlib.sha256(extension.read_bytes()).hexdigest(),
            "engine_fixture_sha256": hashlib.sha256(engine.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--extension", type=Path, required=True)
    parser.add_argument("--record", type=Path)
    arguments = parser.parse_args()
    result = run(arguments.extension.resolve())
    if arguments.record:
        arguments.record.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("native observation: replaced Path factory, OS byte roundtrip and manual records passed")


if __name__ == "__main__":
    main()
