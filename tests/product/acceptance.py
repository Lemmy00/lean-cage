#!/usr/bin/env python3
"""Exercise the built public product, with all workloads inside owned disposable VMs."""
# §FS-linux-product.acceptance: Caller Python/shell, denial, cancellation, storage and channel loss.
import argparse
import copy
import hashlib
import json
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "python"))
from leancage import Workspace, Cancellation
from leancage.build import DEFAULT_BUNDLE, sha, source_inventory

CASES = ["python_check", "python_run_and_report", "shell_check", "shell_run_and_report",
         "policy_rejection", "denied_effect", "bounded_output_and_forged_control_bytes",
         "vm_report_storage_failure", "host_publication_failure",
         "lost_result_channel_preserves_observations", "vm_loss_before_any_observation",
         "cli_cancellation_and_descendant_cleanup"]


def check_evidence(api, path):
    """Reuse the passed public run only for its exact bundle, sources and scenarios."""
    evidence = json.loads(path.read_text())
    if (evidence.get("schema") != "leancage-product-vm-evidence-v1" or
            evidence.get("status") != "passed" or evidence.get("bundle_id") != api.bundle_id or
            evidence.get("manifest_sha256") != sha(api.bundle / "manifest.json") or
            evidence.get("machine") != api.manifest["machine"] or
            evidence.get("source_sha256") != api.manifest["source_sha256"] or
            source_inventory() != api.manifest["source_sha256"] or
            evidence.get("test_sha256") != sha(Path(__file__)) or
            [row.get("name") for row in evidence.get("cases", [])] != CASES):
        raise ValueError("public acceptance receipt differs from the current bundle, inputs or scenarios")
    print("Passed public CLI/library acceptance receipt matches the current identified bundle.", flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bundle", type=Path, default=DEFAULT_BUNDLE)
    parser.add_argument("--record", type=Path, default=ROOT / "assurance/product-vm-evidence.json")
    parser.add_argument("--check-evidence", action="store_true",
                        help="verify the existing passed receipt without repeating its VM executions")
    args = parser.parse_args()
    api = Workspace(args.bundle)
    if args.check_evidence:
        check_evidence(api, args.record)
        return
    records = []
    base = json.loads((ROOT / "profiles/offline-workspace/example-policy.json").read_text())
    began = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="product-acceptance-", dir=ROOT / ".tools") as directory:
        work = Path(directory)
        results = ROOT / ".tools/product/acceptance" / api.bundle_id
        api.results = results

        def policy(name, code, shell=False, **changes):
            value = copy.deepcopy(base)
            value["argv"] = ["/bin/sh" if shell else "/usr/local/bin/python3", "-c", code]
            value.update(changes)
            path = work / (name + ".json")
            path.write_text(json.dumps(value))
            return path

        def public(command, path, *extra, expected=0, staged=False):
            entry = args.bundle / "bin/leancage" if staged else ROOT / "leancage"
            command_line = [str(entry), "--bundle", str(args.bundle), "--results", str(results), command, str(path), *map(str, extra)]
            completed = subprocess.run(command_line, cwd=ROOT, capture_output=True, text=True, timeout=120)
            allowed = expected if isinstance(expected, tuple) else (expected,)
            if completed.returncode not in allowed:
                raise AssertionError(f"public {command} exit {completed.returncode}: {completed.stdout} {completed.stderr}")
            return json.loads(completed.stdout)

        def record(name, result):
            value = result.json() if hasattr(result, "json") else result
            records.append(dict(name=name, result=value))
            print(name + ": passed", flush=True)

        input_args = ("--workspace", ROOT / "examples/workspace/input", "--stdin", ROOT / "examples/workspace/stdin.txt")
        python = ROOT / "examples/workspace/python-policy.json"
        shell = ROOT / "examples/workspace/shell-policy.json"
        for name, path in (("python", python), ("shell", shell)):
            checked = public("check", path, *input_args, staged=name == "shell")
            assert checked["status"] == "complete" and checked["report"]["entry"] == "no"
            record(name + "_check", checked)
            result = public("run", path, *input_args, staged=name == "shell")
            assert result["status"] == "complete" and result["report"]["entry"] == "yes" and result["report"]["cleanup"] == "complete"
            target = Path(result["output"])
            if name == "python":
                assert json.loads((target / "export/summary.json").read_text()) == dict(sum=42, stdin="caller stdin")
                assert (target / "stdout").read_bytes() == b"python-workflow\n"
                assert (target / "stderr").read_bytes() == b"python-stderr\n"
            else:
                assert (target / "export/answer.txt").read_bytes() == b"caller workspace / caller stdin\n"
                assert (target / "stdout").read_bytes() == b"shell-workflow"
            retrieved = public("report", result["request_id"], staged=name == "shell")
            assert retrieved == result
            assert json.loads((target / "vm-report.json").read_bytes()) == result["report"]
            assert (target / "stored-report.json").read_bytes() == (target / "vm-report.json").read_bytes()
            record(name + "_run_and_report", result)

        invalid = work / "invalid.json"
        invalid.write_text('{"schema_version":1,"schema_version":1}')
        rejected = public("run", invalid, expected=64)
        assert rejected["status"] == "rejected" and rejected["entry"] == "no"
        record("policy_rejection", rejected)
        denied = policy("denied", "import socket,errno;\ntry: socket.socket()\nexcept OSError as error: assert error.errno==errno.EPERM; print('denied-as-requested')\nelse: raise AssertionError('network unexpectedly admitted')")
        denied_result = public("run", denied)
        assert Path(denied_result["output"], "stdout").read_bytes() == b"denied-as-requested\n"
        record("denied_effect", denied_result)

        bounded = policy("bounded", "import os; os.write(1,b'LCVM1\\0\\0\\0'+b'x'*4096); os.write(2,b'e'*2048)")
        value = json.loads(bounded.read_text())
        value["limits"].update(stdout_max_bytes=64, stderr_max_bytes=32)
        bounded.write_text(json.dumps(value))
        bounded_result = public("run", bounded, expected=(124, 137))
        assert bounded_result["report"]["stdout_truncated"] and bounded_result["report"]["cancellation_bits"] & 8
        assert bounded_result["artifacts"]["stdout"]["bytes"] == 64 and bounded_result["artifacts"]["stderr"]["bytes"] <= 32
        assert Path(bounded_result["output"], "stdout").read_bytes().startswith(b"LCVM1\0\0\0")
        record("bounded_output_and_forged_control_bytes", bounded_result)

        storage = policy("storage", "import time; print('known-execution'); time.sleep(.3)")
        failure = api.run(storage, _test_fault="report-storage")
        assert failure.status == "complete", failure.json()
        assert failure.report["entry"] == "yes" and failure.report["cleanup"] == "complete" and failure.report["report_storage"] == "failed"
        assert failure.exit_code == 126 and failure.stdout == b"known-execution\n"
        record("vm_report_storage_failure", failure)
        blocker = work / "blocked"
        blocker.write_text("preserve")
        failure = api.run(storage, output=blocker / "result")
        assert failure.publication == "failed" and failure.report["entry"] == "yes" and failure.report["cleanup"] == "complete"
        assert blocker.read_text() == "preserve"
        record("host_publication_failure", failure)

        lost = api.run(storage, _test_fault="channel-loss")
        assert lost.status == "incomplete" and lost.vm_cleanup == "complete", lost.json()
        assert lost.report["entry"] == "yes" and lost.report["cleanup"] == "complete"
        assert lost.json()["artifacts"]["stdout"] is None
        record("lost_result_channel_preserves_observations", lost)

        early = api.run(storage, timeout=0.001)
        assert early.status == "incomplete" and early.report is None and early.vm_cleanup == "complete", early.json()
        record("vm_loss_before_any_observation", early)

        slow = policy("cancellation", "import os,time;\nif os.fork()==0: time.sleep(120)\nelse: print('ready',flush=True); time.sleep(120)")
        value = json.loads(slow.read_text()); value["limits"]["wall_time_ms"] = 60000
        slow.write_text(json.dumps(value))
        process = subprocess.Popen([str(ROOT / "leancage"), "--bundle", str(args.bundle), "--results", str(results), "run", str(slow)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            time.sleep(8)
            process.send_signal(signal.SIGTERM)
            stdout, stderr = process.communicate(timeout=35)
        except BaseException:
            process.kill(); process.wait(); raise
        cancelled = json.loads(stdout)
        assert cancelled["status"] == "complete" and cancelled["report"]["entry"] == "yes" and cancelled["report"]["cleanup"] == "complete", (cancelled, stderr)
        assert cancelled["report"]["cancellation_bits"] & 1 and cancelled["vm_cleanup"] == "complete"
        assert cancelled["report"]["termination"] in ("cancelled", "signaled")
        record("cli_cancellation_and_descendant_cleanup", cancelled)

        identities = [row["result"].get("request_id") for row in records if row["result"].get("request_id")]
        assert len(identities) == len(set(identities))
        # Exercise the staged, relocatable entry as well as the repository entry.
        bundled = subprocess.run([str(args.bundle / "bin/leancage"), "bundle"], capture_output=True, text=True, check=True)
        assert json.loads(bundled.stdout)["bundle_id"] == api.bundle_id
    if [row["name"] for row in records] != CASES or source_inventory() != api.manifest["source_sha256"]:
        raise ValueError("public acceptance scenarios or bundle sources changed during the run")
    evidence = dict(schema="leancage-product-vm-evidence-v1", status="passed", bundle_id=api.bundle_id,
                    manifest_sha256=sha(args.bundle / "manifest.json"), elapsed_seconds=round(time.monotonic()-began, 3),
                    cases=records, machine=api.manifest["machine"], source_sha256=api.manifest["source_sha256"],
                    test_sha256=sha(Path(__file__)), validation="public CLI and shared library; real QEMU VMs; no host guest execution")
    args.record.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(f"Product acceptance passed: {len(records)} scenarios; bundle {api.bundle_id}", flush=True)


if __name__ == "__main__":
    main()
