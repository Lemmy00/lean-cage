"""Exercise native argument roots through ordinary callbacks and the public CPython API."""
# §AR-host-boundary.interfaces.gateway: Kwargs mutation must not invalidate captured arguments.
import argparse
import gc
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import weakref


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def run(extension, bundle, caller):
    native = module("_host", extension)
    invoke = module("_gateway_call", caller).call
    events = []

    class PathArgument:
        def __init__(self, name, value):
            self.name, self.value = name, str(value)

        def __fspath__(self):
            events.append("path:" + self.name)
            return self.value

        def __del__(self):
            events.append("released:" + self.name)

    class TimeoutArgument:
        def __float__(self):
            events.append("timeout")
            return 1.0

        def __del__(self):
            events.append("released:timeout")

    def release_check(references):
        gc.collect()
        assert all(reference() is None for reference in references.values()), events

    with tempfile.TemporaryDirectory(prefix="leancage-native-arguments-") as temporary:
        area = Path(temporary)
        malformed = area / "policy.json"
        malformed.write_text("{broken", encoding="utf-8")
        inputs = area / "inputs"
        inputs.mkdir()
        stdin = area / "stdin"
        stdin.write_bytes(b"ordinary input")

        for fail in (False, True):
            keywords = {"results": PathArgument("constructor-results", area / "results")}
            references = {name: weakref.ref(value) for name, value in keywords.items()}

            class BundleArgument:
                def __fspath__(self):
                    keywords.clear()
                    gc.collect()
                    assert all(reference() is not None for reference in references.values())
                    if fail:
                        raise ValueError("ordinary constructor callback failure")
                    return str(bundle)

            keywords["bundle"] = BundleArgument()
            if fail:
                try:
                    invoke(native.Workspace, (), keywords)
                except ValueError as error:
                    assert str(error) == "ordinary constructor callback failure"
                else:
                    raise AssertionError("constructor callback failure was ignored")
            else:
                api = invoke(native.Workspace, (), keywords)
                assert api.results == area / "results"
            release_check(references)

        for method in ("run", "check"):
            for fail in (False, True):
                keywords = {
                    "workspace": PathArgument("workspace", inputs),
                    "stdin": PathArgument("stdin", stdin),
                    "output": PathArgument("output", area / "output"),
                    "cancellation": native.Cancellation(),
                    "timeout": TimeoutArgument(),
                }
                references = {name: weakref.ref(value) for name, value in keywords.items()
                              if name != "cancellation"}

                class PolicyArgument:
                    def __fspath__(self):
                        keywords.clear()
                        gc.collect()
                        assert all(reference() is not None for reference in references.values())
                        events.append("cleared:" + method)
                        if fail:
                            raise ValueError("ordinary policy callback failure")
                        return str(malformed)

                keywords["policy"] = PolicyArgument()
                try:
                    invoke(getattr(api, method), (), keywords)
                except ValueError as error:
                    if fail:
                        assert str(error) == "ordinary policy callback failure"
                else:
                    raise AssertionError("malformed policy or callback failure was accepted")
                assert not keywords
                release_check(references)

        for method, parameter in (("validate", "policy"), ("report", "request")):
            keywords = {}

            class SingleArgument:
                def __fspath__(self):
                    keywords.clear()
                    gc.collect()
                    events.append("single:" + method)
                    raise ValueError("ordinary single-argument callback failure")

            keywords[parameter] = SingleArgument()
            reference = weakref.ref(keywords[parameter])
            try:
                invoke(getattr(api, method), (), keywords)
            except ValueError as error:
                assert str(error) == "ordinary single-argument callback failure"
            else:
                raise AssertionError("single-argument callback failure was ignored")
            release_check({parameter: reference})

        keywords = {name: PathArgument("outcome-" + name, area / name) for name in
                    ("request_id", "bundle_id", "command", "status", "report", "exit_code", "vm_cleanup")}
        references = {name: weakref.ref(value) for name, value in keywords.items()}
        presentation = invoke(native.Outcome, (), keywords)
        keywords.clear()
        for name, reference in references.items():
            assert getattr(presentation, name) is reference()
        del presentation
        release_check(references)

    return {"schema": "leancage-host-native-argument-roots-v1", "events": events,
            "interpreter": sys.version, "extension_sha256": hashlib.sha256(extension.read_bytes()).hexdigest(),
            "caller_sha256": hashlib.sha256(caller.read_bytes()).hexdigest(), "bundle": str(bundle)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--extension", type=Path, required=True)
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--caller", type=Path, required=True)
    parser.add_argument("--record", type=Path)
    arguments = parser.parse_args()
    record = run(arguments.extension.resolve(), arguments.bundle.resolve(), arguments.caller.resolve())
    if arguments.record:
        arguments.record.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print("native argument roots: constructor, run/check, validate/report callbacks and Outcome lifetimes passed")


if __name__ == "__main__":
    main()
