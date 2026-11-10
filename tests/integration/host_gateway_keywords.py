"""Compare fixed-signature native argument selection with the preceding public parser."""
# §AR-host-boundary.interfaces.gateway: Preserve public call shapes through source refactoring.
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


class SelectedBundle(Exception):
    pass


class BundleArgument:
    def __fspath__(self):
        raise SelectedBundle("selected caller bundle")


def observations(native, invoke):
    workspace = native.Workspace.__new__(native.Workspace)
    selected = BundleArgument()
    calls = []

    def data(value):
        if isinstance(value, bytes):
            return {"bytes_hex": value.hex()}
        if isinstance(value, list):
            return [data(item) for item in value]
        if isinstance(value, dict):
            return {name: data(item) for name, item in value.items()}
        return value

    def observe(name, function, positional=(), keywords=None, project=None):
        try:
            result = invoke(function, positional, {} if keywords is None else keywords)
        except BaseException as error:
            value = {"exception": type(error).__name__}
        else:
            value = {"value": data(project(result)) if project else "returned"}
        calls.append((name, value))

    for name in ("run", "check", "validate", "report"):
        function = getattr(workspace, name)
        policy_key = "request" if name == "report" else "policy"
        observe(name + ":missing", function)
        observe(name + ":positional", function, (b"{}",))
        observe(name + ":keyword", function, keywords={policy_key: b"{}"})
        observe(name + ":duplicate", function, (b"{}",), {policy_key: b"{}"})
        observe(name + ":extra-positional", function, (b"{}", b"extra"))
        observe(name + ":unknown", function, (b"{}",), {"unknown": None})
        observe(name + ":nonstring", function, (b"{}",), {42: None})
        if name in ("run", "check"):
            observe(name + ":optional", function, (b"{}",), {
                "workspace": None, "stdin": None, "output": None,
                "cancellation": None, "timeout": None,
            })
            observe(name + ":fault", function, (b"{}",), {"_test_fault": "channel-loss"})

    for name, positional, keywords in (
        ("positional", (selected,), {}),
        ("keyword", (), {"bundle": selected}),
        ("two-positional", (selected, None), {}),
        ("duplicate", (selected,), {"bundle": selected}),
        ("unknown", (), {"bundle": selected, "unknown": None}),
        ("nonstring", (), {42: None}),
        ("extra-positional", (selected, None, None), {}),
    ):
        observe("Workspace:" + name, native.Workspace, positional, keywords)

    observe("Cancellation:empty", native.Cancellation, project=lambda value: value.is_set())
    observe("Cancellation:positional", native.Cancellation, (None,))
    observe("Cancellation:keyword", native.Cancellation, keywords={"unknown": None})
    observe("Cancellation:nonstring", native.Cancellation, keywords={42: None})

    fields = ("request_id", "bundle_id", "command", "status", "report", "exit_code", "vm_cleanup",
              "error", "stdout", "stderr", "files", "output", "publication", "publication_error")
    required = ("request", "bundle", "run", "returned", None, 0, "complete")
    all_values = required + (None, b"", b"", {}, None, "not-requested", None)
    project = lambda value: [getattr(value, name) for name in fields]
    observe("Outcome:required", native.Outcome, required, project=project)
    observe("Outcome:all-positional", native.Outcome, all_values, project=project)
    observe("Outcome:all-keywords", native.Outcome, keywords=dict(zip(fields, all_values)), project=project)
    observe("Outcome:missing", native.Outcome, required[:-1])
    observe("Outcome:duplicate", native.Outcome, required, {"status": "duplicate"})
    observe("Outcome:unknown", native.Outcome, required, {"unknown": None})
    observe("Outcome:nonstring", native.Outcome, required, {42: None})
    observe("Outcome:extra-positional", native.Outcome, all_values + (None,))
    observe("cli:duplicate", native.cli, ([],), {"argv": []})
    observe("cli:unknown", native.cli, keywords={"unknown": None})
    observe("cli:extra-positional", native.cli, ([], []))
    observe("cli:nonstring", native.cli, keywords={42: None})
    return calls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--caller", type=Path, required=True)
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    invoke = load("_gateway_call", args.caller).call
    baseline = observations(load("_host", args.baseline), invoke)
    candidate = observations(load("_host", args.candidate), invoke)
    differences = [(old, new) for old, new in zip(baseline, candidate) if old != new]
    assert len(baseline) == len(candidate) and not differences, differences
    # These tests stop before engine dispatch; valid calls on uninitialized
    # Workspace records must pass parsing and reach the real initialization guard.
    for name, value in candidate:
        if name.endswith(":positional") and name.split(":")[0] in ("run", "check", "validate", "report"):
            assert value == {"exception": "RuntimeError"}, (name, value)
    record = {
        "status": "passed", "python": sys.version, "cases": len(candidate),
        "baseline_sha256": hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
        "candidate_sha256": hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
        "observations": candidate,
    }
    if args.record:
        args.record.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"native keyword selection: {len(candidate)} matching public call shapes")


if __name__ == "__main__":
    main()
