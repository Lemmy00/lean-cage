#!/usr/bin/env python3
"""Exercise real initializer callbacks, failed imports, retries and cached imports."""
# §AR-host-boundary.primitives: Ordinary callbacks cannot replace the native class globals.
# §FS-host-boundary.caller.initialization: Repeated direct initialization fails before setup.
import importlib.util
import json
from pathlib import Path
import pathlib
import subprocess
import sys
import types


def load(extension, name):
    spec = importlib.util.spec_from_file_location(name, extension)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def useful(module):
    assert all(isinstance(getattr(module, name), type)
               for name in ("Workspace", "Outcome", "Cancellation"))
    token = module.Cancellation()
    assert not token.is_set()
    token.cancel()
    assert token.is_set()


def worker(extension, mode):
    original = sys.modules["pathlib"]
    real_path = pathlib.Path
    events = []
    class Callback(types.ModuleType):
        def __getattr__(self, name):
            if name != "Path":
                raise AttributeError(name)
            events.append("path callback")
            if mode == "failure":
                raise ValueError("injected path lookup failure")
            try:
                load(extension, "nested._host")
            except ImportError as error:
                assert "already in progress" in str(error), str(error)
                events.append("nested entry rejected")
                if mode == "nested_failure":
                    raise
            else:
                raise AssertionError("nested initializer returned a module")
            return real_path

    sys.modules["pathlib"] = Callback("pathlib")
    try:
        if mode == "nested":
            module = load(extension, "initial._host")
        else:
            try:
                load(extension, "initial._host")
            except (ImportError, ValueError) as error:
                expected = "already in progress" if mode == "nested_failure" else "injected path lookup failure"
                assert expected in str(error), str(error)
                events.append("outer failure observed")
            else:
                raise AssertionError("injected initialization failure returned a module")
            sys.modules["pathlib"] = original
            module = load(extension, "initial._host")
            events.append("sequential retry succeeded")
        useful(module)
        cached = load(extension, "initial._host")
        assert cached.Outcome is module.Outcome
        events.append("cached import kept classes")
        try:
            load(extension, "different._host")
        except ImportError as error:
            assert "already initialized" in str(error), str(error)
            events.append("later direct entry rejected")
        else:
            raise AssertionError("later direct initializer replaced native classes")
        useful(module)
        print(json.dumps(dict(case=mode, events=events, success=True,
                              scope="real native initializer; no engine or VM executed")))
    finally:
        sys.modules["pathlib"] = original


def main():
    if len(sys.argv) == 4 and sys.argv[1] == "--worker":
        worker(str(Path(sys.argv[3]).resolve()), sys.argv[2])
        return
    if len(sys.argv) != 2:
        raise SystemExit("usage: host_gateway_initialization.py IDENTIFIED_EXTENSION")
    extension = str(Path(sys.argv[1]).resolve(strict=True))
    for case in ("nested", "failure", "nested_failure"):
        completed = subprocess.run([sys.executable, str(Path(__file__).resolve()), "--worker", case, extension],
                                   text=True, capture_output=True, timeout=15)
        print(completed.stdout, end="")
        if completed.returncode:
            print(completed.stderr, end="", file=sys.stderr)
            completed.check_returncode()


if __name__ == "__main__":
    main()
