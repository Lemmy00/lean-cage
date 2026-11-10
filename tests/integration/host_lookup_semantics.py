#!/usr/bin/env python3
"""Check the current host lookup guard in an isolated casefold-capable VM."""

# §AR-host-boundary.primitives: No host mounts, inode-flag changes, NIC or guest execution.
from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess


ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / ".tools/host/lookup-vm"
EVIDENCE = ROOT / "assurance/host-lookup-vm-evidence.json"
PINS = ROOT / "tests/vm/bootstrap-pins.json"
BASE_CONFIG = ROOT / "tests/vm/linux-6.18.59.config"
SPEC = importlib.util.spec_from_file_location("lookup_vm_bootstrap", ROOT / "scripts/run_m1_vm.py")
BOOT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BOOT)
REQUIRED = (
    "BLOCK", "BLK_DEV", "PCI", "PCI_MSI", "VIRTIO_MENU", "VIRTIO", "VIRTIO_PCI",
    "VIRTIO_PCI_LEGACY", "VIRTIO_BLK", "EXT4_FS", "UNICODE", "TMPFS_XATTR",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(arguments, **options):
    return subprocess.run([str(value) for value in arguments], cwd=ROOT, check=True, **options)


def sources() -> dict[str, str]:
    paths = {
        Path(__file__).resolve(), ROOT / "tests/vm/host_lookup_init.c", PINS, BASE_CONFIG,
        ROOT / "linux/host_primitives.c", ROOT / "verification/host/FilesystemAccessNative.lean",
        ROOT / "host/lean-toolchain", ROOT / "host/lake-manifest.json",
        ROOT / "scripts/run_m1_vm.py",
    }
    pending = [ROOT / "verification/host/FilesystemAccessNative.lean"]
    while pending:
        path = pending.pop()
        for name in re.findall(r"^import (LeanCageHost(?:\.[A-Za-z0-9_]+)+)\s*$", path.read_text(), re.M):
            dependency = ROOT / "host" / (name.replace(".", "/") + ".lean")
            if dependency not in paths:
                paths.add(dependency)
                pending.append(dependency)
    return {str(path.relative_to(ROOT)): digest(path) for path in sorted(paths)}


def prepare_kernel(prepare: bool) -> Path:
    pins = json.loads(PINS.read_text())
    archive = ROOT / ".tools/m1vm" / f'linux-{pins["kernel_version"]}.tar.xz'
    if digest(archive) != pins["kernel_archive_sha256"]:
        raise ValueError("pinned kernel archive identity differs")
    kernel = WORK / "kernel"
    if not kernel.exists():
        if not prepare:
            raise ValueError("run with --prepare to build the isolated lookup-test kernel")
        kernel.mkdir(parents=True)
        run(["tar", "--extract", "--xz", "--file", archive, "--strip-components=1", "--directory", kernel])
        (kernel / ".lookup-source-sha256").write_text(pins["kernel_archive_sha256"] + "\n")
    if (kernel / ".lookup-source-sha256").read_text().strip() != pins["kernel_archive_sha256"]:
        raise ValueError("the isolated kernel source is not the pinned extraction")
    boot = kernel / "arch/x86/boot/bzImage"
    if boot.exists():
        actual = (kernel / ".config").read_text()
        if all(f"CONFIG_{name}=y\n" in actual for name in REQUIRED):
            return kernel
    if not prepare:
        raise ValueError("the isolated lookup-test kernel requires --prepare")
    shutil.copyfile(BASE_CONFIG, kernel / ".config")
    for name in REQUIRED:
        run([kernel / "scripts/config", "--file", kernel / ".config", "--enable", name])
    run([kernel / "scripts/config", "--file", kernel / ".config", "--set-str", "LOCALVERSION", "-leancage-lookup"])
    tools = ROOT / ".tools/m1vm/root"
    environment = dict(os.environ, PATH=f"{tools}/usr/bin:/usr/bin:/bin",
                       M4=f"{tools}/usr/bin/m4", BISON_PKGDATADIR=f"{tools}/usr/share/bison",
                       HOSTCFLAGS=f"-O2 -I{tools}/usr/include", HOSTLDFLAGS=f"-L{tools}/usr/lib/x86_64-linux-gnu",
                       KBUILD_BUILD_TIMESTAMP="2026-11-09 00:00:00 UTC", KBUILD_BUILD_USER="leancage",
                       KBUILD_BUILD_HOST="disposable-host-lookup", KBUILD_BUILD_VERSION="1")
    with (WORK / "kernel-build.log").open("w") as log:
        run(["nice", "-n", "10", "make", "-C", kernel, "-j2", "ARCH=x86_64", "olddefconfig", "bzImage"],
            env=environment, stdout=log, stderr=subprocess.STDOUT)
    actual = (kernel / ".config").read_text()
    if not all(f"CONFIG_{name}=y\n" in actual for name in REQUIRED):
        raise ValueError("the generated test configuration omitted a required filesystem feature")
    return kernel


def build_image() -> Path:
    run(["lake", "-d", "host", "build", "filesystem-access-check"])
    init = WORK / "init"
    run(["cc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-static",
         ROOT / "tests/vm/host_lookup_init.c", "-o", init])
    executable = ROOT / "host/.lake/build/bin/filesystem-access-check"
    files = [("/filesystem-access-check", executable),
             *((str(path), path) for path in BOOT.dependencies(executable))]
    entries = []
    directories = {"dev", "newroot"}
    for name, path in files:
        for parent in Path(name).parents:
            if str(parent) != "/":
                directories.add(str(parent).lstrip("/"))
        entries.append((name.lstrip("/"), stat.S_IFREG | 0o555, path.read_bytes(), 0, 0))
    entries.extend([
        ("init", stat.S_IFREG | 0o555, init.read_bytes(), 0, 0),
        ("inventory", stat.S_IFREG | 0o444, ("".join(name + "\n" for name, _ in files)).encode(), 0, 0),
        ("leancage-host-lookup-vm", stat.S_IFREG | 0o444, b"isolated-host-lookup-v1\n", 0, 0),
        ("dev/console", stat.S_IFCHR | 0o600, b"", 5, 1),
        ("dev/null", stat.S_IFCHR | 0o666, b"", 1, 3),
    ])
    image = WORK / "initramfs.cpio.gz"
    image.write_bytes(BOOT.cpio([(name, stat.S_IFDIR | 0o755, b"", 0, 0)
                                for name in sorted(directories)] + entries))
    return image


def validate_log(text: str, returncode: int) -> None:
    expected = ["useful path=/plain", "useful path=/case/plain", "casefold path=/case/folded",
                "unsupported path=/proc"]
    if returncode != 33 or "LOOKUP_VM_COMPLETE cases=4 failures=0" not in text or "LOOKUP_VM_FAILURE" in text:
        raise ValueError("disposable lookup VM did not finish successfully")
    if "LOOKUP_ALIAS actual_same_object=1 casefold=1 reserved_lowercase_stage=1" not in text:
        raise ValueError("the actual casefold private-name alias was not exercised")
    for case in expected:
        if f"LOOKUP_CASE mode={case} exit=0" not in text:
            raise ValueError(f"missing actual guard case: {case}")


def check_artifacts() -> None:
    record = json.loads(EVIDENCE.read_text())
    if record.get("status") != "passed" or record["sources_sha256"] != sources():
        raise ValueError("lookup VM receipt does not match current runtime/fixture inputs")
    for path, expected in record["artifacts_sha256"].items():
        if digest(ROOT / path) != expected:
            raise ValueError(f"changed lookup VM artifact: {path}")
    transcript = gzip.decompress((ROOT / record["transcript"]).read_bytes()).decode(errors="replace")
    validate_log(transcript, record["returncode"])
    print("current lookup guard matches the recorded isolated-VM four-case pass")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("--check-artifacts", action="store_true")
    arguments = parser.parse_args()
    if arguments.check_artifacts:
        if arguments.prepare:
            parser.error("--prepare and --check-artifacts are exclusive")
        check_artifacts()
        return
    WORK.mkdir(parents=True, exist_ok=True)
    kernel = prepare_kernel(arguments.prepare)
    image = build_image()
    disk = WORK / "casefold.ext4"
    with disk.open("wb") as output:
        output.truncate(64 * 1024 * 1024)
    run(["mkfs.ext4", "-q", "-F", "-O", "casefold", "-E", "encoding=utf8", disk])
    tools = ROOT / ".tools/m1vm/root"
    qemu = tools / "usr/bin/qemu-system-x86_64"
    firmware = tools / "usr/share/seabios/bios-256k.bin"
    environment = dict(os.environ, LD_LIBRARY_PATH=str(tools / "usr/lib/x86_64-linux-gnu"),
                       QEMU_MODULE_DIR=str(tools / "usr/lib/x86_64-linux-gnu/qemu"))
    command = [qemu, "-L", tools / "usr/share/qemu", "-no-user-config", "-nodefaults",
               "-machine", "pc,accel=tcg", "-cpu", "max", "-smp", "1", "-m", "4096M", "-bios", firmware,
               "-display", "none", "-serial", "stdio", "-monitor", "none", "-nic", "none", "-no-reboot",
               "-snapshot", "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
               "-drive", f"file={disk},if=none,format=raw,id=lookupdisk", "-device", "virtio-blk-pci,drive=lookupdisk",
               "-kernel", kernel / "arch/x86/boot/bzImage", "-initrd", image,
               "-append", "console=ttyS0,115200 rdinit=/init panic=1 oops=panic loglevel=5"]
    runtime_sources = sources()
    EVIDENCE.write_text(json.dumps({"schema": 1, "status": "running", "sources_sha256": runtime_sources}) + "\n")
    transcript = WORK / "transcript.log"
    with transcript.open("w") as output:
        completed = subprocess.run([str(value) for value in command], cwd=ROOT, env=environment,
                                   stdout=output, stderr=subprocess.STDOUT, timeout=180)
    text = transcript.read_text(errors="replace")
    validate_log(text, completed.returncode)
    sealed = ROOT / "assurance/host-lookup-vm-transcript.log.gz"
    sealed.write_bytes(gzip.compress(transcript.read_bytes(), mtime=0))
    artifacts = [kernel / ".config", kernel / "arch/x86/boot/bzImage", image, disk, qemu, firmware,
                 ROOT / "host/.lake/build/bin/filesystem-access-check", WORK / "init", sealed]
    artifacts.extend(BOOT.dependencies(qemu, environment))
    record = {
        "schema": 1, "status": "passed", "scope": "targeted filesystem guard; not M5.2 delivery acceptance",
        "sources_sha256": runtime_sources, "returncode": completed.returncode,
        "transcript": str(sealed.relative_to(ROOT)),
        "artifacts_sha256": {str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path): digest(path)
                             for path in sorted(set(artifacts))},
        "configuration": {"kernel": "pinned6.18.59-derived-ext4-casefold", "extra_features": REQUIRED,
                          "host_mounts": False, "host_inode_flag_changes": False, "network": False,
                          "acceleration": "tcg", "ephemeral_snapshot_disk": True,
                          "memory_mib": 4096, "lean_workers": 0, "lean_main_stack_kib": 8192,
                          "runtime_initializer_stack": "Lean libuv initializes before lean_run_main reads stack size",
                          "command": [str(value) for value in command]},
        "cases": ["tmpfs-useful", "ext4-useful", "actual-casefold-alias-and-rename-denial", "procfs-denial"],
    }
    EVIDENCE.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print("isolated VM: actual casefold alias denied, rename not reached, tmpfs/ext4 useful, unsupported procfs denied")


if __name__ == "__main__":
    main()
