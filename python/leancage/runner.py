"""Shared public API: validate, freeze, execute, reap, and publish one request."""
# §AR-workspace-vm.lifetime: The host owns exactly one VM and its private result socket.
from dataclasses import dataclass, field
import ctypes
import json
import os
from pathlib import Path
import re
import signal
import socket
import stat
import struct
import subprocess
import tempfile
import threading
import time
import uuid

from .build import DEFAULT_BUNDLE, ROOT, load, sha
from .protocol import Decoder, REPORT, STORED, STDOUT, STDERR, EXPORT, strict_json
from .snapshots import snapshot, parse_export, write_exports, read_regular, digest

REQUEST = struct.Struct("<8s32s64sIQQQQIQ")


class Cancellation:
    def __init__(self):
        self.event = threading.Event()

    def cancel(self):
        self.event.set()


@dataclass
class Outcome:
    request_id: str
    bundle_id: str
    command: str
    status: str
    report: dict | None
    exit_code: int
    vm_cleanup: str
    error: str | None = None
    stdout: bytes = b""
    stderr: bytes = b""
    files: dict = field(default_factory=dict)
    output: Path | None = None
    publication: str = "pending"
    publication_error: str | None = None

    def json(self):
        return dict(schema="leancage-workspace-v1", request_id=self.request_id, bundle_id=self.bundle_id,
                    command=self.command, status=self.status, report=self.report, exit_code=self.exit_code,
                    vm_cleanup=self.vm_cleanup, error=self.error, publication=self.publication,
                    publication_error=self.publication_error, output=str(self.output) if self.output else None,
                    artifacts={"complete": self.status == "complete",
                               "stdout": {"bytes": len(self.stdout), "sha256": digest(self.stdout)} if self.status == "complete" else None,
                               "stderr": {"bytes": len(self.stderr), "sha256": digest(self.stderr)} if self.status == "complete" else None,
                               "files": {name: {"bytes": len(data), "sha256": digest(data)} for name, data in self.files.items()}})


def rename_new(source, target):
    libc = ctypes.CDLL(None, use_errno=True)
    rename = libc.renameat2
    rename.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    rename.restype = ctypes.c_int
    if rename(-100, os.fsencode(source), -100, os.fsencode(target), 1):
        number = ctypes.get_errno()
        raise OSError(number, os.strerror(number), str(target))


class Workspace:
    """Execute caller policies in the identified bundle. Never execute a guest on the host."""

    def __init__(self, bundle=DEFAULT_BUNDLE, results=None):
        self.bundle = Path(bundle).absolute()
        self.results = Path(results).absolute() if results is not None else ROOT / ".tools/product/runs"
        manifest_bytes = read_regular(self.bundle / "manifest.json", 4*1024*1024)
        self.manifest = strict_json(manifest_bytes)
        self.bundle_id = digest(manifest_bytes)
        if self.manifest.get("schema") != "leancage-bundle-v1":
            raise ValueError("unsupported bundle; run scripts/build.sh")
        for name, expected in self.manifest["files"].items():
            if name.startswith("/") or any(part in ("", ".", "..") for part in name.split("/")):
                raise ValueError("noncanonical bundle path")
            path = self.bundle / name
            if path.is_symlink() or not path.is_file() or sha(path) != expected:
                raise ValueError("bundle component identity differs: " + name)
        for name, expected in self.manifest["source_sha256"].items():
            if name.startswith("python/leancage/"):
                actual = Path(__file__).parent / Path(name).name
                if sha(actual) != expected:
                    raise ValueError("host library changed; rebuild the bundle")

    def _controller_environment(self):
        directories = sorted({str(p.parent) for p in (self.bundle / "lib").rglob("*") if p.is_file()})
        return dict(PATH="/usr/bin:/bin", LC_ALL="C", LD_LIBRARY_PATH=":".join(directories))

    def validate(self, policy):
        raw = policy if isinstance(policy, bytes) else read_regular(policy, 65536)
        if len(raw) > 65536:
            raise ValueError("policy exceeds 65536 bytes")
        with tempfile.TemporaryDirectory(prefix="leancage-policy-") as directory:
            path = Path(directory) / "policy.json"
            path.write_bytes(raw)
            result = subprocess.run([str(self.bundle / "bin/controller"), "validate-policy", str(path)],
                                    env=self._controller_environment(), capture_output=True, timeout=30)
        if result.returncode:
            raise ValueError(result.stdout[:65536].decode("utf-8", "replace").strip() or "policy rejected")
        return strict_json(raw)

    def check(self, policy, *, workspace=None, stdin=None, output=None, cancellation=None, timeout=None):
        return self._execute("check", policy, workspace, stdin, output, cancellation, timeout)

    def run(self, policy, *, workspace=None, stdin=None, output=None, cancellation=None, timeout=None, _test_fault=None):
        return self._execute("run", policy, workspace, stdin, output, cancellation, timeout, _test_fault)

    def _execute(self, command, policy, workspace, stdin, output, cancellation, timeout, test_fault=None):
        request_id = uuid.uuid4().hex
        value = self.validate(policy)
        frozen = snapshot(workspace, stdin, value["limits"])
        for key, identity in (("workspace_input", frozen.workspace_identity), ("stdin_input", frozen.stdin_identity)):
            if value[key] is not None and value[key] != identity:
                raise ValueError("supplied snapshot differs from policy " + key)
            value[key] = identity
        raw = json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode()
        self.validate(raw)
        if test_fault not in (None, "report-storage", "channel-loss"):
            raise ValueError("unknown acceptance fault")
        limits = value["limits"]
        deadline_seconds = timeout if timeout is not None else 60 + limits["wall_time_ms"] / 1000
        if deadline_seconds <= 0 or deadline_seconds > 3660:
            raise ValueError("VM timeout is outside the supported bound")
        decoder = Decoder(request_id, self.bundle_id, limits)
        cleanup, error, code = "unknown", None, 126
        cancel = cancellation if cancellation is not None else Cancellation()
        boot_log = b""
        with tempfile.TemporaryDirectory(prefix="leancage-vm-") as directory:
            work = Path(directory)
            bootstrap = load("workspace_cpio", "scripts/run_m1_vm.py")
            entries = [("request", stat.S_IFDIR | 0o700, b"", 0, 0),
                       ("m3-inputs/trees", stat.S_IFDIR | 0o700, b"", 0, 0),
                       ("m3-inputs/blobs", stat.S_IFDIR | 0o700, b"", 0, 0),
                       ("request/policy.json", stat.S_IFREG | 0o400, raw, 0, 0)]
            config = REQUEST.pack(b"LCREQ1\0\0", request_id.encode(), self.bundle_id.encode(), 1 if command == "check" else 2,
                                  limits["stdout_max_bytes"], limits["stderr_max_bytes"], limits["workspace_max_bytes"],
                                  limits["workspace_max_inodes"], {None: 0, "report-storage": 1, "channel-loss": 2}[test_fault], 0)
            entries.append(("request/config", stat.S_IFREG | 0o400, config, 0, 0))
            if frozen.tree is not None:
                entries.append(("m3-inputs/trees/" + digest(frozen.tree), stat.S_IFREG | 0o400, frozen.tree, 0, 0))
            entries.extend(("m3-inputs/blobs/" + key, stat.S_IFREG | 0o400, data, 0, 0) for key, data in sorted(frozen.blobs.items()))
            image = work / "request.cpio.gz"
            with image.open("wb") as target, (self.bundle / "profile/runtime.cpio.gz").open("rb") as base:
                import shutil
                shutil.copyfileobj(base, target)
                target.write(bootstrap.cpio(entries))
            socket_path = work / "control.sock"
            emulator = self.bundle / "emulator"
            args = [str(emulator / "usr/bin/qemu-system-x86_64"), "-L", str(emulator / "usr/share/qemu"),
                    "-no-user-config", "-nodefaults", "-machine", "pc,accel=tcg", "-cpu", "max", "-smp", "1", "-m", "2048M",
                    "-bios", str(emulator / "usr/share/seabios/bios-256k.bin"), "-display", "none", "-monitor", "none", "-nic", "none", "-no-reboot",
                    "-serial", "file:" + str(work / "boot.log"),
                    "-chardev", "socket,id=control,path=" + str(socket_path) + ",server=on,wait=on", "-serial", "chardev:control",
                    "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04", "-kernel", str(self.bundle / "profile/kernel"),
                    "-initrd", str(image), "-append", "console=ttyS0,115200 rdinit=/init panic=1 oops=panic loglevel=3 clocksource=acpi_pm tsc=unstable"]
            env = dict(PATH="/usr/bin:/bin", LC_ALL="C", LD_LIBRARY_PATH=str(emulator / "usr/lib/x86_64-linux-gnu"),
                       QEMU_MODULE_DIR=str(emulator / "usr/lib/x86_64-linux-gnu/qemu"))
            process, connection = None, None
            began, sent = time.monotonic(), None
            try:
                with (work / "emulator.log").open("wb") as diagnostic:
                    process = subprocess.Popen(args, env=env, stdin=subprocess.DEVNULL, stdout=diagnostic, stderr=diagnostic, start_new_session=True)
                    connection = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                    connection.settimeout(0.1)
                    while True:
                        try:
                            connection.connect(str(socket_path)); break
                        except (FileNotFoundError, ConnectionRefusedError):
                            if process.poll() is not None:
                                raise ValueError("VM failed to start: " + (work / "emulator.log").read_text(errors="replace")[:2048])
                            if time.monotonic() - began > min(15, deadline_seconds):
                                raise TimeoutError("VM control channel did not open")
                            time.sleep(0.02)
                    while True:
                        now = time.monotonic()
                        if cancel.event.is_set() and sent is None:
                            connection.sendall(b"C"); sent = now
                        if now - began > deadline_seconds or (sent is not None and now - sent > 15):
                            raise TimeoutError("VM deadline or cancellation grace expired")
                        for log in (work / "boot.log", work / "emulator.log"):
                            if log.exists() and log.stat().st_size > 4*1024*1024:
                                raise ValueError("VM diagnostic bound exceeded")
                        try:
                            chunk = connection.recv(65536)
                        except socket.timeout:
                            continue
                        if not chunk:
                            break
                        decoder.feed(chunk)
                    controller_exit, retrieval_exit, transport_error, extinct = decoder.finish()
                    process.wait(timeout=10)
                    if process.returncode != 33 or transport_error:
                        raise ValueError("VM ended without a successful complete transport")
                    code = controller_exit
                    self._validate_result(decoder, command, retrieval_exit, extinct, value)
            except (ValueError, OSError, TimeoutError, subprocess.TimeoutExpired) as failure:
                error = str(failure)
            finally:
                if connection is not None:
                    connection.close()
                if process is not None:
                    if process.poll() is None:
                        try:
                            os.killpg(process.pid, signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                        try:
                            process.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            try:
                                os.killpg(process.pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                            process.wait(timeout=5)
                    cleanup = "complete" if process.returncode is not None else "unknown"
                else:
                    cleanup = "not_started"
                if (work / "boot.log").exists():
                    with (work / "boot.log").open("rb") as diagnostics:
                        boot_log = diagnostics.read(4*1024*1024)
        observed = self._known_report(decoder.report, command)
        result = Outcome(request_id, self.bundle_id, command, "complete" if error is None else "incomplete", observed,
                         code if error is None else 126, cleanup, error)
        export_entries, directories = [], []
        if error is None:
            result.stdout = decoder.records.get(STDOUT, b"")
            result.stderr = decoder.records.get(STDERR, b"")
            if EXPORT in decoder.records:
                export_entries, directories = parse_export(decoder.records[EXPORT], observed["export_digest"], decoder.blobs, limits)
                result.files = {name: data for name, data, _ in export_entries}
        self._publish(result, raw, boot_log, decoder, export_entries, directories, output)
        return result

    @staticmethod
    def _known_report(report, command):
        if not isinstance(report, dict) or report.get("schema") != "leancage-result-v1":
            return None
        if report.get("run_id") not in (0, 1):
            return None
        if command == "check" and (report.get("entry") != "no" or
                                   (report.get("run_id") != 0 and report.get("termination") != "setup_failed")):
            return None
        if report.get("entry") not in ("no", "yes", "unknown") or report.get("cleanup") not in ("complete", "unknown"):
            return None
        return report

    def _validate_result(self, decoder, command, retrieval_exit, extinct, policy):
        report = self._known_report(decoder.report, command)
        if report is None or report.get("profile") != self.manifest["profile"] or report.get("runtime_manifest_digest") != self.manifest["runtime_manifest_digest"]:
            raise ValueError("returned report does not match the requested profile/run")
        if report.get("cleanup") == "complete" and extinct != 1:
            raise ValueError("cleanup report disagrees with the owned VM scope")
        if command == "check":
            if decoder.blobs or any(tag in decoder.records for tag in (STORED, STDOUT, STDERR, EXPORT)):
                raise ValueError("preflight returned workload artifacts")
            return
        if report.get("run_id") == 1:
            if report.get("report_storage") == "stored":
                if retrieval_exit or decoder.records.get(STORED) != decoder.records[REPORT]:
                    raise ValueError("report retrieval differs from the requested run")
            elif STORED in decoder.records:
                raise ValueError("failed report storage returned a published report")
            for tag, name in ((STDOUT, "stdout"), (STDERR, "stderr")):
                content = decoder.records.get(tag)
                count = report.get(name + "_captured_bytes")
                if count is not None and ((content is None and (count != 0 or report.get("entry") == "yes")) or
                                          (content is not None and len(content) != count)):
                    raise ValueError("capture bytes differ from the run report")
            if report.get("export") == "complete":
                if EXPORT not in decoder.records:
                    raise ValueError("missing promised export")
                parse_export(decoder.records[EXPORT], report.get("export_digest"), decoder.blobs, policy["limits"])
            elif decoder.blobs or EXPORT in decoder.records:
                raise ValueError("uncommitted export artifacts")

    def _publish(self, result, policy, boot_log, decoder, entries, directories, output):
        target = Path(output).absolute() if output is not None else self.results / result.request_id
        try:
            target.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
            with tempfile.TemporaryDirectory(prefix=".publish-", dir=target.parent) as directory:
                stage = Path(directory) / "result"
                stage.mkdir(mode=0o700)
                if result.status == "complete":
                    (stage / "stdout").write_bytes(result.stdout)
                    (stage / "stderr").write_bytes(result.stderr)
                (stage / "policy.json").write_bytes(policy)
                (stage / "boot.log").write_bytes(boot_log)
                if result.report is not None:
                    (stage / "vm-report.json").write_bytes(decoder.records[REPORT])
                if result.status == "complete" and STORED in decoder.records:
                    (stage / "stored-report.json").write_bytes(decoder.records[STORED])
                (stage / "export").mkdir(mode=0o700)
                write_exports(stage / "export", entries, directories)
                result.output, result.publication = target, "stored"
                (stage / "result.json").write_text(json.dumps(result.json(), indent=2, sort_keys=True) + "\n")
                rename_new(stage, target)
        except (OSError, ValueError) as error:
            result.output, result.publication = None, "failed"
            result.publication_error = str(error)
            result.exit_code = 126

    def report(self, request):
        text = str(request)
        target = self.results / text if re.fullmatch("[0-9a-f]{32}", text) else Path(text).absolute()
        data = strict_json(read_regular(target / "result.json", 4*1024*1024))
        if data.get("schema") != "leancage-workspace-v1" or data.get("bundle_id") != self.bundle_id:
            raise ValueError("stored result belongs to another bundle")
        if re.fullmatch("[0-9a-f]{32}", text) and data.get("request_id") != text:
            raise ValueError("stored result belongs to another request")
        for name in ("stdout", "stderr"):
            info = data["artifacts"][name]
            if info is None:
                continue
            raw = read_regular(target / name, 16777216)
            if len(raw) != info["bytes"] or digest(raw) != info["sha256"]:
                raise ValueError("stored capture identity differs")
        for name, info in data["artifacts"]["files"].items():
            from .snapshots import path_bytes
            path_bytes(name, reserved=False)
            raw = read_regular(target / "export" / name, 268435456)
            if len(raw) != info["bytes"] or digest(raw) != info["sha256"]:
                raise ValueError("stored export identity differs")
        return data
