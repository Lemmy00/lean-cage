"""Stage the exact VM controller, helper, runtime and emulator used by callers."""
# §AR-workspace-vm.bundle: Reuse pinned preparation and image primitives, not a second runtime.
import argparse
import hashlib
import importlib.util
import json
import os
import platform
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BUNDLE = ROOT / ".tools/product/bundle"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as source:
        for data in iter(lambda: source.read(1024 * 1024), b""):
            h.update(data)
    return h.hexdigest()


def source_inventory():
    paths = [ROOT / name for name in ("linux/workspace.c", "linux/vm_init.c", "linux/artifacts.h",
             "linux/filter.h", "linux/sha256.h", "scripts/build.sh", "scripts/run_m1_vm.py", "leancage",
             "lean-toolchain", "lakefile.lean", "lake-manifest.json", "LeanCage.lean",
             "workspace/Main.lean", "workspace/LeanCageM3.lean", "workspace/lakefile.lean",
             "workspace/lake-manifest.json", "workspace/lean-toolchain", "lifecycle/LeanCageM2.lean",
             "lifecycle/lakefile.lean", "lifecycle/lake-manifest.json", "lifecycle/lean-toolchain",
             "library/lakefile.lean", "library/lake-manifest.json", "library/lean-toolchain")]
    paths += sorted((ROOT / "LeanCage").rglob("*.lean"))
    paths += sorted((ROOT / "python/leancage").glob("*.py"))
    paths += sorted((ROOT / "library").glob("*.lean"))
    paths += sorted((ROOT / "workspace/LeanCageM3").glob("*.lean"))
    paths += sorted((ROOT / "lifecycle/LeanCageM2").rglob("*.lean"))
    return {str(p.relative_to(ROOT)): sha(p) for p in paths}


def image_entries(runtime):
    # Keep the same reviewed runtime overlays as the existing workspace profile.
    for prefix in ("tmp", "var/tmp", "run", "dev", "proc", "sys", "workspace", "etc/machine-id"):
        runtime = {n: e for n, e in runtime.items() if n != prefix and not n.startswith(prefix + "/")}
    for name in ("run", "dev", "proc", "sys", "workspace"):
        runtime[name] = dict(kind="directory", mode=0o755, data=b"")
    for name in ("tmp", "var/tmp"):
        runtime[name] = dict(kind="symlink", mode=0o777, data=b"/workspace/.tmp")
    for name in ("passwd", "group", "hostname", "hosts", "resolv.conf"):
        runtime["etc/" + name] = dict(kind="file", mode=0o444, data=b"")
    runtime_module = load("workspace_runtime_build", "scripts/workspace_runtime.py")
    runtime[".leancage-runtime"] = dict(kind="file", mode=0o444, data=runtime_module.load_lock()["manifest_digest"].encode())
    entries = [(name, stat.S_IFDIR | (0o700 if name in ("m3-runs", "m3-results", "m3-inputs") else 0o755), b"", 0, 0)
               for name in ("dev", "proc", "sys", "m3-runs", "m3-results", "m3-inputs", "m3-runtime")]
    for name, entry in sorted(runtime.items(), key=lambda row: (row[0].count("/"), row[0])):
        kind = {"directory": stat.S_IFDIR, "file": stat.S_IFREG, "symlink": stat.S_IFLNK}[entry["kind"]]
        entries.append(("m3-runtime/" + name, kind | entry["mode"], entry["data"], 0, 0))
    return entries


def build(destination=DEFAULT_BUNDLE, prepare=True):
    if sys.platform != "linux" or os.uname().machine != "x86_64":
        raise ValueError("the supported bundle requires Linux x86-64")
    original_sources = source_inventory()
    if not (ROOT / "assurance/product-core.json").is_file():
        raise ValueError("the checked product core record is missing")
    vm = load("workspace_vm_baseline", "scripts/run_m3_vm.py")
    bootstrap = vm.M1
    if not (vm.WORK / "linux-6.18.59/arch/x86/boot/bzImage").is_file() or not (vm.WORK / "root/usr/bin/qemu-system-x86_64").is_file():
        if not prepare:
            raise ValueError("pinned VM tools are missing; run scripts/build.sh")
        vm.prepare()
    bootstrap.check_hash(vm.WORK / "linux-6.18.59/.config", sha(vm.CONFIG))
    pins = json.loads(bootstrap.PINS.read_text())
    for package in pins["packages"]:
        bootstrap.check_hash(vm.WORK / "packages" / package["filename"], package["sha256"])
    runtime_module = load("workspace_runtime_bundle", "scripts/workspace_runtime.py")
    runtime = runtime_module.load_entries(fetch=prepare)
    elf = load("workspace_elf_bundle", "scripts/elf_closure.py")
    if elf.inventory(runtime, runtime_module.resolve) != json.loads((ROOT / "profiles/offline-workspace/elf-closure.json").read_text()):
        raise ValueError("runtime ELF closure differs from the reviewed profile")
    subprocess.run(["lake", "build", "leancage"], cwd=ROOT / "workspace", check=True)
    subprocess.run(["lake", "build"], cwd=ROOT / "library", check=True)
    destination = Path(destination).absolute()
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="bundle-", dir=destination.parent) as directory:
        stage = Path(directory) / "bundle"
        stage.mkdir()
        for name in ("bin", "lib", "emulator", "profile", "assurance"):
            (stage / name).mkdir()
        shutil.copy2(ROOT / "LICENSE", stage / "LICENSE")
        shutil.copy2(ROOT / "tests/vm/bootstrap-pins.json", stage / "profile/bootstrap-pins.json")
        shutil.copytree(ROOT / "python/leancage", stage / "python/leancage", ignore=shutil.ignore_patterns("__pycache__"))
        (stage / "scripts").mkdir()
        shutil.copy2(ROOT / "scripts/run_m1_vm.py", stage / "scripts/run_m1_vm.py")
        (stage / "bin/leancage").write_text('#!/usr/bin/env python3\nfrom pathlib import Path\nimport sys\nsys.path.insert(0, str(Path(__file__).resolve().parents[1] / "python"))\nfrom leancage.cli import main\nraise SystemExit(main(["--bundle", str(Path(__file__).resolve().parents[1]), *sys.argv[1:]]))\n')
        (stage / "bin/leancage").chmod(0o755)
        for name, source in (("helper", "linux/workspace.c"), ("init", "linux/vm_init.c")):
            subprocess.run(["cc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-static", "-no-pie",
                            str(ROOT / source), "-o", str(stage / "bin" / name)], check=True)
        controller = ROOT / "workspace/.lake/build/bin/leancage"
        shutil.copy2(controller, stage / "bin/controller")
        subprocess.run([str(controller), "emit-filter", str(stage / "profile/filter.bin")], check=True)
        if (ROOT / "linux/filter.h").read_text() != vm.filter_header((stage / "profile/filter.bin").read_bytes()):
            raise ValueError("native filter differs from the proved Lean filter bytes")
        entries = image_entries(runtime)
        directories = set()
        for library in bootstrap.dependencies(controller):
            name = str(library).lstrip("/")
            directories.update(str(p) for p in Path(name).parents if str(p) != ".")
            entries.append((name, stat.S_IFREG | 0o555, library.read_bytes(), 0, 0))
            target = stage / "lib" / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(library, target)
        entries[:0] = [(n, stat.S_IFDIR | 0o755, b"", 0, 0) for n in sorted(directories, key=lambda p: (p.count("/"), p))]
        for image_name, staged in (("init", "bin/init"), ("leancage", "bin/controller"),
                                   ("leancage-m3-helper", "bin/helper"), ("filter.bin", "profile/filter.bin")):
            entries.append((image_name, stat.S_IFREG | 0o555, (stage / staged).read_bytes(), 0, 0))
        entries.extend([
            ("leancage-m3-disposable-vm", stat.S_IFREG | 0o444, b"LeanCage-M3-root-VM-v1", 0, 0),
            ("m3-assurance.json", stat.S_IFREG | 0o444, json.dumps({"schema": "leancage-product-trust-v1", "assumptions": vm.ASSUMPTIONS}).encode(), 0, 0),
            ("dev/console", stat.S_IFCHR | 0o600, b"", 5, 1),
            ("dev/ttyS1", stat.S_IFCHR | 0o600, b"", 4, 65),
            ("dev/urandom", stat.S_IFCHR | 0o444, b"", 1, 9),
            ("dev/null", stat.S_IFCHR | 0o666, b"", 1, 3)])
        names = [row[0] for row in entries]
        if len(names) != len(set(names)):
            raise ValueError("duplicate base initramfs path")
        (stage / "profile/runtime.cpio.gz").write_bytes(bootstrap.cpio(entries))
        (stage / "profile/image-inventory.json").write_text(json.dumps({n: {"mode": mode, "sha256": hashlib.sha256(data).hexdigest(), "major": major, "minor": minor}
                                                                  for n, mode, data, major, minor in entries}, indent=2, sort_keys=True) + "\n")
        shutil.copy2(vm.WORK / "linux-6.18.59/arch/x86/boot/bzImage", stage / "profile/kernel")
        shutil.copy2(vm.CONFIG, stage / "profile/kernel.config")
        for name in ("runtime-lock.json", "runtime-config.json", "runtime-manifest.json", "policy.schema.json", "example-policy.json", "syscalls.json", "elf-closure.json"):
            source = ROOT / "profiles/offline-workspace" / name
            if source.exists():
                shutil.copy2(source, stage / "profile" / name)
        emulator_root = vm.WORK / "root"
        # Retain the local emulator module/firmware closure; never depend on a host QEMU install.
        for subdir in ("usr/share/qemu", "usr/share/seabios", "usr/lib/x86_64-linux-gnu/qemu"):
            shutil.copytree(emulator_root / subdir, stage / "emulator" / subdir, symlinks=False)
        shutil.copytree(emulator_root / "usr/share/doc", stage / "emulator/usr/share/doc", symlinks=False)
        qemu = emulator_root / "usr/bin/qemu-system-x86_64"
        (stage / "emulator/usr/bin").mkdir(parents=True)
        shutil.copy2(qemu, stage / "emulator/usr/bin/qemu-system-x86_64")
        qemu_libraries = bootstrap.dependencies(qemu, vm.environment())
        for source in qemu_libraries:
            target = stage / "emulator/usr/lib/x86_64-linux-gnu" / source.name
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                shutil.copy2(source, target)
        for name in ("product-layout.json", "filter-decoder.json", "m2-claims.json", "m3-claims.json",
                     "reporting-source.json.gz", "reporting-connection.json.gz", "reporting-compiler.json.gz", "product-core.json"):
            source = ROOT / "assurance" / name
            if source.exists():
                shutil.copy2(source, stage / "assurance" / name)
        checked_artifacts = {}
        for package in ("", "lifecycle", "workspace", "library"):
            directory = ROOT / package / ".lake/build/lib/lean"
            for path in directory.rglob("*.olean"):
                checked_artifacts[str(path.relative_to(ROOT))] = sha(path)
        files = {str(p.relative_to(stage)): sha(p) for p in sorted(stage.rglob("*")) if p.is_file()}
        current_sources = source_inventory()
        if current_sources != original_sources:
            raise ValueError("product sources changed while the bundle was built")
        manifest = {
            "schema": "leancage-bundle-v1", "profile": vm.PROFILE, "machine": vm.MACHINE,
            "runtime_manifest_digest": runtime_module.load_lock()["manifest_digest"],
            "source_sha256": current_sources, "files": files, "checked_lean_artifacts": checked_artifacts,
            "tools": {"lean": subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT, check=True, capture_output=True, text=True).stdout.strip(),
                      "cc": subprocess.run(["cc", "--version"], check=True, capture_output=True, text=True).stdout.splitlines()[0],
                      "libc": subprocess.run(["getconf", "GNU_LIBC_VERSION"], check=True, capture_output=True, text=True).stdout.strip(),
                      "linker": subprocess.run(["ld", "--version"], check=True, capture_output=True, text=True).stdout.splitlines()[0],
                      "host": platform.freedesktop_os_release(),
                      "qemu": "8.2.2", "kernel": "6.18.59", "seabios": "1.16.3"},
            "proof_bindings": "assurance/product-core.json",
            "trusted_components": {
                "platform": vm.ASSUMPTIONS,
                "native_adapter": {"source": "linux/workspace.c", "functions": {
                    name: re.findall(r"^(?:static )?(?:_Noreturn )?(?:struct \w+|int|void|uint64_t|uint32_t) (\w+)\(", (ROOT / name).read_text(), re.M)
                    for name in ("linux/workspace.c", "linux/artifacts.h", "linux/sha256.h")},
                                   "evidence": "review, existing VM suite, capture regression; complete source correspondence remains an application-verification task"},
                "vm_adapter": {"source": "linux/vm_init.c", "functions": ["profile", "command", "helper_child", "cancel_helper", "send_file", "exports", "scopes_extinct", "main"],
                               "evidence": "public-interface acceptance and bounded protocol tests"},
                "host_adapter": {"source": "python/leancage", "evidence": "snapshot, framing, identity, publication and VM lifetime tests"}},
            "licensing": {"project": "Apache-2.0", "runtime": "upstream notices retained in runtime filesystem; see profile/runtime-lock.json", "qemu": "GPL-2.0 and component notices in pinned Ubuntu packages", "kernel": "GPL-2.0; pinned source and config in tests/vm/bootstrap-pins.json; local development bundle"}}
        (stage / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        backup = destination.with_name(destination.name + ".previous")
        if backup.exists():
            shutil.rmtree(backup)
        if destination.exists():
            destination.rename(backup)
        try:
            stage.rename(destination)
        except BaseException:
            if backup.exists():
                backup.rename(destination)
            raise
        if backup.exists():
            shutil.rmtree(backup)
    print("Bundle ready: " + str(destination))
    return destination


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_BUNDLE)
    parser.add_argument("--no-prepare", action="store_true")
    args = parser.parse_args()
    build(args.output, not args.no_prepare)


if __name__ == "__main__":
    main()
