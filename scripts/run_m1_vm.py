#!/usr/bin/env python3
"""Build and run only the disposable M1 VM; never execute the guest on the host."""

# §AR-m1-launch.vm: Pinned local tooling, ephemeral RAM image, no host mounts or NIC.

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import struct
import subprocess
import sys
import urllib.request


PROJECT = Path(__file__).resolve().parents[1]
WORK = PROJECT / ".tools/m1vm"
PINS = PROJECT / "tests/vm/bootstrap-pins.json"
CONFIG = PROJECT / "tests/vm/linux-6.18.59.config"
TRANSCRIPT = PROJECT / "assurance/m1-vm-transcript.log"
EVIDENCE = PROJECT / "assurance/m1-vm-evidence.json"
EXPECTED = {
    "allowed_and_denied": (0, "kind=0 phase=0 detail=0 receipts=0", True),
    "empty": (64, "kind=validation error=LeanCage.Linux.Filter.DecodeError.emptyInput", False),
    "truncated": (64, "kind=validation error=LeanCage.Linux.Filter.DecodeError.misalignedInput 71", False),
    "permissive": (64, "kind=validation error=LeanCage.Linux.Filter.DecodeError.unsupportedInstruction 7", False),
    "oversized": (64, "kind=validation error=LeanCage.Linux.Filter.DecodeError.oversizedInput 32769", False),
    "byte_order": (64, "kind=validation error=LeanCage.Linux.Filter.DecodeError.unsupportedInstruction 0", False),
    "bad_elf": (125, "kind=1 phase=1 detail=8 receipts=0", False),
    "nnp_failure": (125, "kind=1 phase=2 detail=22 receipts=1", False),
    "install_failure": (125, "kind=1 phase=3 detail=22 receipts=3", False),
    "exec_failure": (125, "kind=1 phase=4 detail=13 receipts=15", False),
    "terminated_setup": (143, "kind=2 phase=0 detail=15 receipts=0", False),
    "x32_rejected": (159, "kind=2 phase=0 detail=31 receipts=0", True),
    "i386_rejected": (159, "kind=2 phase=0 detail=31 receipts=0", True),
}
GUEST = "GUEST_RESULT getpid_positive=1 getppid_raw=-1 nnp=1 seccomp=2 uid=65534"


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_identities():
    paths = [PINS, CONFIG, PROJECT / "tests/vm/kernel.fragment", Path(__file__).resolve(),
             PROJECT / "tests/vm/init.c", PROJECT / "tests/vm/guest.c",
             PROJECT / "native/leancage_m1.c", PROJECT / "M1Main.lean", PROJECT / "LeanCage.lean",
             PROJECT / "lakefile.lean", PROJECT / "lean-toolchain", PROJECT / "lake-manifest.json",
             *sorted((PROJECT / "LeanCage").rglob("*.lean"))]
    return {str(path.relative_to(PROJECT)): sha256(path) for path in paths}


def run(command, **kwargs):
    return subprocess.run([str(item) for item in command], cwd=PROJECT, check=True, **kwargs)


def check_hash(path, expected):
    if not path.is_file() or sha256(path) != expected:
        raise ValueError(f"Missing or changed pinned input: {path}")


def prepare(pins):
    """Extract .debs locally and build the guest kernel, without host installation."""
    host = platform.freedesktop_os_release()
    if (platform.machine() != pins["host_arch"] or host.get("ID") != pins["host_distribution"]
            or host.get("VERSION_ID") != pins["host_version"]):
        raise ValueError("The bootstrap supports only the recorded Ubuntu 24.04 x86-64 host")
    packages = WORK / "packages"
    packages.mkdir(parents=True, exist_ok=True)
    root = WORK / "root"
    root.mkdir(exist_ok=True)
    for package in pins["packages"]:
        path = packages / package["filename"]
        if not path.exists():
            subprocess.run(["apt-get", "download", f'{package["name"]}={package["version"]}'],
                           cwd=packages, check=True)
        check_hash(path, package["sha256"])
        run(["dpkg-deb", "--extract", path, root], stdout=subprocess.DEVNULL)
    archive = WORK / f'linux-{pins["kernel_version"]}.tar.xz'
    if not archive.exists():
        temporary = archive.with_suffix(".download")
        urllib.request.urlretrieve(pins["kernel_archive_url"], temporary)
        check_hash(temporary, pins["kernel_archive_sha256"])
        temporary.replace(archive)
    check_hash(archive, pins["kernel_archive_sha256"])
    kernel = WORK / f'linux-{pins["kernel_version"]}'
    # A fresh source/build tree prevents cached objects from hiding local source changes.
    if kernel.exists():
        shutil.rmtree(kernel)
    run(["tar", "--extract", "--xz", "--file", archive, "--directory", WORK])
    shutil.copyfile(CONFIG, kernel / ".config")
    environment = dict(os.environ, PATH=f"{root}/usr/bin:/usr/bin:/bin",
                       M4=f"{root}/usr/bin/m4", BISON_PKGDATADIR=f"{root}/usr/share/bison",
                       HOSTCFLAGS=f"-O2 -I{root}/usr/include",
                       HOSTLDFLAGS=f"-L{root}/usr/lib/x86_64-linux-gnu",
                       PKG_CONFIG_PATH=f"{root}/usr/lib/x86_64-linux-gnu/pkgconfig",
                       KBUILD_BUILD_TIMESTAMP="2026-10-30 00:00:00 UTC",
                       KBUILD_BUILD_USER="leancage", KBUILD_BUILD_HOST="disposable-m1",
                       KBUILD_BUILD_VERSION="1")
    with (WORK / "kernel-build.log").open("w") as log:
        subprocess.run(["nice", "-n", "10", "make", "-j2", "ARCH=x86_64", "olddefconfig", "bzImage"],
                       cwd=kernel, env=environment, stdout=log, stderr=subprocess.STDOUT, check=True)
    check_hash(kernel / ".config", sha256(CONFIG))


def dependencies(binary, environment=None):
    """Read trusted build output's shared-library map; do not run a guest workload."""
    output = run(["ldd", binary], capture_output=True, text=True, env=environment).stdout
    if "not found" in output:
        raise ValueError(f"Unresolved shared libraries for {binary}:\n{output}")
    return sorted({Path(path) for path in re.findall(r"(?:=>\s+|^\s*)(/\S+)", output, re.M)})


def cpio(entries):
    """Encode newc, including VM device nodes without privileged host mknod."""
    output = bytearray()
    for inode, (name, mode, data, major, minor) in enumerate(entries + [
            ("TRAILER!!!", 0, b"", 0, 0)], 1):
        encoded = name.encode() + b"\0"
        fields = [inode, mode, 0, 0, 1, 0, len(data), 0, 0, major, minor, len(encoded), 0]
        output.extend(b"070701" + "".join(f"{value:08x}" for value in fields).encode())
        output.extend(encoded)
        output.extend(b"\0" * (-len(output) % 4))
        output.extend(data)
        output.extend(b"\0" * (-len(output) % 4))
    return gzip.compress(bytes(output), mtime=0)


def build_image():
    run(["lake", "build", "leancage-m1"])
    for name in ("guest", "init"):
        run(["cc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-static", "-no-pie",
             PROJECT / f"tests/vm/{name}.c", "-o", WORK / name])
    rows = [(0x20, 0, 0, 4), (0x15, 1, 0, 0xc000003e), (6, 0, 0, 0x80000000),
            (0x20, 0, 0, 0), (0x35, 0, 1, 0x40000000), (6, 0, 0, 0x80000000),
            (0x15, 0, 1, 110), (6, 0, 0, 0x50001), (6, 0, 0, 0x7fff0000)]
    canonical = b"".join(struct.pack("<HBBI", *row) for row in rows)
    permissive = bytearray(canonical)
    permissive[60:64] = struct.pack("<I", 0x7fff0000)
    byte_order = bytearray(canonical)
    byte_order[0:2] = reversed(byte_order[0:2])
    entries = []
    directories = set()

    def add(name, data, permissions=0o444):
        for parent in Path(name).parents:
            if str(parent) != ".":
                directories.add(str(parent))
        entries.append((name, stat.S_IFREG | permissions, data, 0, 0))

    launcher = PROJECT / ".lake/build/bin/leancage-m1"
    add("leancage-m1", launcher.read_bytes(), 0o555)
    for library in dependencies(launcher):
        add(str(library).lstrip("/"), library.read_bytes(), 0o555)
    add("init", (WORK / "init").read_bytes(), 0o555)
    add("guest", (WORK / "guest").read_bytes(), 0o555)
    add("guest-noexec", (WORK / "guest").read_bytes())
    add("bad-elf", b"not an ELF executable\n", 0o555)
    add("leancage-m1-disposable-vm", b"LeanCage-M1-VM-v1")
    for name, data in {"filter.bin": canonical, "empty.bin": b"", "truncated.bin": canonical[:-1],
                       "permissive.bin": permissive, "oversized.bin": bytes(32769),
                       "byte-order.bin": byte_order}.items():
        add(name, bytes(data))
    directories.update(("dev", "proc", "sys", "tmp"))
    entries[:0] = [(name, stat.S_IFDIR | (0o1777 if name == "tmp" else 0o755), b"", 0, 0)
                   for name in sorted(directories, key=lambda item: (item.count("/"), item))]
    entries += [("dev/console", stat.S_IFCHR | 0o600, b"", 5, 1),
                ("dev/null", stat.S_IFCHR | 0o666, b"", 1, 3),
                ("dev/urandom", stat.S_IFCHR | 0o444, b"", 1, 9)]
    image = WORK / "initramfs.cpio.gz"
    image.write_bytes(cpio(entries))
    files = {"/" + name: hashlib.sha256(data).hexdigest()
             for name, mode, data, _, _ in entries if stat.S_ISREG(mode)}
    return image, files


# §FS-filter-loading.claim: Require positive guest evidence and exact error/termination cases.
def validate_transcript(transcript, return_code):
    transcript = transcript.replace("\r", "")
    if return_code != 33 or transcript.count("VM_COMPLETE cases=13 failures=0\n") != 1:
        raise ValueError("VM did not report all 13 cases passing and exit via isa-debug-exit")
    if "VM_PROFILE kernel=6.18.59 machine=x86_64 pid1_uid=0\n" not in transcript:
        raise ValueError("Missing pinned VM profile")
    matches = list(re.finditer(r"^CASE_BEGIN name=(\w+)\n(.*?)^CASE_END name=(\w+) exit=(\d+) expected=(\d+)\n",
                               transcript, re.M | re.S))
    if [match[1] for match in matches] != list(EXPECTED):
        raise ValueError("Missing, duplicate, or reordered VM cases")
    records = []
    for match in matches:
        name, body, end_name, exit_code, expected_code = match.groups()
        expected_exit, diagnostic, guest = EXPECTED[name]
        if name != end_name or int(exit_code) != expected_exit or int(expected_code) != expected_exit:
            raise ValueError(f"Unexpected VM case exit: {name}")
        results = [line for line in body.splitlines() if line.startswith("M1_RESULT ")]
        guests = [line for line in body.splitlines() if line.startswith("GUEST_RESULT ")]
        if results != ["M1_RESULT " + diagnostic] or guests != ([GUEST] if guest else []):
            raise ValueError(f"Unexpected VM evidence or guest execution: {name}: {body}")
        records.append({"name": name, "exit_code": expected_exit, "diagnostic": diagnostic,
                        "guest_observed": guest, "passed": True})
    if transcript.count("M1_RESULT ") != 13 or transcript.count("GUEST_RESULT ") != 3:
        raise ValueError("Unattributed guest or launcher evidence outside cases")
    return records


# §AR-m1-launch.audit: Validate archived source-bound evidence without running a guest.
def check_evidence():
    evidence = json.loads(EVIDENCE.read_text())
    if evidence.get("schema_version") != 1 or evidence.get("status") != "passed":
        raise ValueError("No passing M1 VM evidence")
    if evidence["source_sha256"] != source_identities():
        raise ValueError("VM sources differ from the recorded demonstration; rerun the VM")
    if evidence["transcript_sha256"] != sha256(TRANSCRIPT):
        raise ValueError("VM transcript identity differs")
    cases = validate_transcript(TRANSCRIPT.read_text(), evidence["return_code"])
    if evidence["cases"] != cases:
        raise ValueError("Structured VM results differ from the raw transcript")
    print(f"Archived M1 VM evidence matches current sources: {len(cases)} passing cases; no VM rerun.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true", help="download pinned local tools and build the VM kernel")
    parser.add_argument("--check-evidence", action="store_true", help="check the archived source/transcript identities; do not boot a VM")
    args = parser.parse_args()
    if args.check_evidence:
        if args.prepare:
            parser.error("--prepare and --check-evidence are mutually exclusive")
        check_evidence()
        return
    pins = json.loads(PINS.read_text())
    WORK.mkdir(parents=True, exist_ok=True)
    if args.prepare:
        prepare(pins)
    for package in pins["packages"]:
        check_hash(WORK / "packages" / package["filename"], package["sha256"])
    kernel = WORK / f'linux-{pins["kernel_version"]}'
    check_hash(WORK / f'linux-{pins["kernel_version"]}.tar.xz', pins["kernel_archive_sha256"])
    check_hash(kernel / ".config", sha256(CONFIG))
    qemu = WORK / "root/usr/bin/qemu-system-x86_64"
    firmware = WORK / "root/usr/share/seabios/bios-256k.bin"
    environment = dict(os.environ, LD_LIBRARY_PATH=f"{WORK}/root/usr/lib/x86_64-linux-gnu",
                       QEMU_MODULE_DIR=f"{WORK}/root/usr/lib/x86_64-linux-gnu/qemu")
    sources = source_identities()
    image, guest_files = build_image()
    command = [str(qemu), "-L", str(WORK / "root/usr/share/qemu"),
               "-no-user-config", "-nodefaults", "-machine", "pc,accel=tcg",
               "-cpu", "max", "-smp", "1", "-m", "2048M", "-bios", str(firmware),
               "-display", "none", "-serial", "stdio", "-monitor", "none", "-nic", "none",
               "-no-reboot", "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
               "-kernel", str(kernel / "arch/x86/boot/bzImage"), "-initrd", str(image),
               "-append", "console=ttyS0,115200 rdinit=/init panic=1 oops=panic loglevel=5"]
    TRANSCRIPT.parent.mkdir(exist_ok=True)
    # Clear an earlier pass before starting; a timeout must not leave a passing record.
    EVIDENCE.write_text(json.dumps({"schema_version": 1, "status": "running"}) + "\n")
    try:
        with TRANSCRIPT.open("w") as log:
            result = subprocess.run(command, cwd=PROJECT, env=environment, stdout=log,
                                    stderr=subprocess.STDOUT, timeout=180)
        transcript = TRANSCRIPT.read_text(errors="replace")
    except subprocess.TimeoutExpired as error:
        EVIDENCE.write_text(json.dumps({"schema_version": 1, "status": "timeout",
                                       "transcript_sha256": sha256(TRANSCRIPT)}) + "\n")
        raise ValueError(f"VM timed out; inspect {TRANSCRIPT}") from error
    try:
        cases = validate_transcript(transcript, result.returncode)
    except ValueError:
        EVIDENCE.write_text(json.dumps({"schema_version": 1, "status": "failed",
                                       "return_code": result.returncode,
                                       "transcript_sha256": sha256(TRANSCRIPT)}) + "\n")
        raise
    artifacts = [qemu, firmware, kernel / "arch/x86/boot/bzImage", kernel / ".config", image,
                 WORK / "root/usr/share/qemu/kvmvapic.bin",
                 WORK / "root/usr/share/qemu/linuxboot_dma.bin",
                 WORK / "root/usr/lib/x86_64-linux-gnu/qemu/accel-tcg-x86_64.so",
                 WORK / "init", WORK / "guest", PROJECT / ".lake/build/bin/leancage-m1"]
    artifacts.extend(dependencies(qemu, environment))
    if sources != source_identities():
        raise ValueError("VM sources changed during the demonstration; rerun without concurrent edits")
    lean_prefix = Path(run(["lake", "env", "lean", "--print-prefix"], capture_output=True, text=True).stdout.strip())
    artifacts.extend(path for path in [lean_prefix / "bin/lean", lean_prefix / "bin/clang",
                                       lean_prefix / "lib/lean/libleanrt.a"] if path.is_file())
    evidence = {
        "schema_version": 1, "status": "passed", "scope": "M1 functional Linux VM demonstration; not isolation or hardware security",
        "kernel": {"version": pins["kernel_version"], "commit": pins["kernel_commit"],
                   "archive_sha256": pins["kernel_archive_sha256"]},
        "qemu_version": run([qemu, "--version"], env=environment, capture_output=True, text=True).stdout.strip(),
        "compiler": run(["cc", "--version"], capture_output=True, text=True).stdout.strip(),
        "libc_version": run(["getconf", "GNU_LIBC_VERSION"], capture_output=True, text=True).stdout.strip(),
        "lean_version": run(["lake", "env", "lean", "--version"], capture_output=True, text=True).stdout.strip(),
        "host_distribution": platform.freedesktop_os_release(),
        "virtual_cpu": [line for line in transcript.replace("\r", "").splitlines() if line.startswith("VM_CPU ")],
        "machine": {"acceleration": "tcg", "cpu": "max", "vcpus": 1, "memory_mib": 2048,
                    "host_mounts": [], "network_devices": [], "persistent_disks": []},
        "launcher_environment": ["LC_ALL=C", "LEAN_NUM_THREADS=1", "LEAN_STACK_SIZE_KB=8192"],
        "command": command, "environment": {key: environment[key] for key in ("LD_LIBRARY_PATH", "QEMU_MODULE_DIR")},
        "return_code": result.returncode, "timeout_seconds": 180, "cases": cases,
        "source_sha256": sources,
        "artifacts_sha256": {str(path): sha256(path) for path in sorted(set(artifacts))},
        "guest_files_sha256": guest_files, "transcript_sha256": sha256(TRANSCRIPT),
        "remaining_assumptions": ["Linux seccomp and syscall enforcement", "C/Lean compiler, runtime, FFI and ELF loader correspondence",
                                  "Trusted entry state, static executable and stable file contents", "Emulator, firmware and hardware fidelity"],
    }
    EVIDENCE.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(f"M1 VM passed: {len(cases)} cases; allowed getpid, denied getppid, fail-closed setup, ABI rejection.")
    print(f"Evidence: {EVIDENCE.relative_to(PROJECT)}; transcript: {TRANSCRIPT.relative_to(PROJECT)}")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"M1 VM failed: {error}", file=sys.stderr)
        sys.exit(1)
