#!/usr/bin/env python3
"""Exercise the candidate entry route in a separate disposable VM image only."""
# §AR-entry.acceptance: Route evidence is separate from completed admission/product acceptance.
import argparse
from datetime import datetime, timezone
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import stat
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / ".tools/launch/prototype"
sys.path.insert(0, str(ROOT / "python"))
from leancage.build import load, image_entries

EVIDENCE = ROOT / "assurance/entry-route-vm.json"
TRANSCRIPT = ROOT / "assurance/entry-route-transcript.log.gz"
INVENTORY = ROOT / "assurance/entry-route-image.json.gz"
SOURCES = ROOT / "assurance/entry-route-sources.tar.gz"
SELECTED = ("shell", "python", "preflight", "fault_nnp_fail", "fault_filter_fail", "fault_exec_fail",
            "fault_credentials_fail", "fault_handles_fail", "fault_error_drop", "fault_error_short", "inherited_handles",
            "fault_release_eof", "fault_release_bad", "fault_release_detach", "fault_parent_reap_fail",
            "fault_admission_clock_fail", "fault_launch_clock_fail", "fault_admission_open_fail")


def selected_vm():
    vm = load("entry_vm", "scripts/run_m3_vm.py")
    # The maintained validator applies unchanged to this explicit focused cohort.
    vm.CASES.CASES = [c for c in vm.CASES.CASES if c["name"] in SELECTED]
    if {c["name"] for c in vm.CASES.CASES} != set(SELECTED):
        raise ValueError("entry prototype cohort differs")
    return vm


def inputs(vm):
    paths = [ROOT / name for name in vm.source_identities()]
    paths += [ROOT / name for name in (
        "linux/workspace.c", "linux/entry_handoff.h", "linux/entry_primitives.c",
        "linux/entry_decimal.h", "linux/entry_decimal.c", "linux/entry_handles.c", "linux/process_primitives.h",
        "linux/process_primitives.c",
        "linux/artifacts.h", "linux/filter.h", "linux/sha256.h", "python/leancage/build.py",
        "scripts/workspace_runtime.py", "profiles/offline-workspace/example-policy.json",
        "launch/lakefile.lean", "launch/lean-toolchain", "launch/lake-manifest.json",
        "tests/entry/prototype.py")]
    paths += [p for directory in ("launch", "workspace", "lifecycle")
              for p in (ROOT / directory).rglob("*.lean") if ".lake" not in p.parts]
    return {str(p.relative_to(ROOT)): vm.M1.sha256(p) for p in sorted(set(paths))}


def archive_sources(sources):
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w") as stream:
        for name, digest in sources.items():
            data = (ROOT / name).read_bytes()
            if hashlib.sha256(data).hexdigest() != digest:
                raise ValueError("source changed before archival: " + name)
            info = tarfile.TarInfo(name)
            info.size = len(data)
            info.mode = 0o644
            stream.addfile(info, io.BytesIO(data))
    return gzip.compress(buffer.getvalue(), mtime=0)


def check_evidence():
    vm = selected_vm()
    record = json.loads(EVIDENCE.read_text())
    if record["schema"] != "leancage-entry-route-prototype-v2" or record["complete_admission"] is not False:
        raise ValueError("not a scoped entry route record")
    if record["sources"] != inputs(vm) or record["machine"] != vm.MACHINE or record["environment"] != vm.environment_record():
        raise ValueError("entry route inputs/configuration differ")
    for key, path in (("transcript_archive_sha256", TRANSCRIPT), ("inventory_archive_sha256", INVENTORY),
                      ("source_archive_sha256", SOURCES)):
        vm.M1.check_hash(path, record[key])
    transcript = gzip.decompress(TRANSCRIPT.read_bytes())
    if hashlib.sha256(transcript).hexdigest() != record["transcript_sha256"]:
        raise ValueError("entry transcript identity differs")
    if vm.validate_transcript(transcript.decode(), record["return_code"]) != record["observations"]:
        raise ValueError("entry observations differ")
    files = json.loads(gzip.decompress(INVENTORY.read_bytes()))
    for name in ("init", "leancage-m3-helper", "leancage-m3-helper-test", "leancage-entry", "leancage-entry-test", "leancage"):
        if files[name]["sha256"] != record["artifacts"][name]:
            raise ValueError("entry image/artifact identity differs: " + name)
    with tarfile.open(SOURCES, "r:gz") as stream:
        members = stream.getmembers()
        if len(members) != len(record["sources"]) or {m.name for m in members} != set(record["sources"]):
            raise ValueError("entry source archive inventory differs")
        for member in members:
            if not member.isfile() or hashlib.sha256(stream.extractfile(member).read()).hexdigest() != record["sources"][member.name]:
                raise ValueError("entry archived source differs: " + member.name)
    print("Entry route evidence checked: focused VM/API/failure paths; complete admission remains unproved.")


def run(record_evidence=False):
    WORK.mkdir(parents=True, exist_ok=True)
    vm = selected_vm()
    sources = inputs(vm)
    source_archive = archive_sources(sources)
    subprocess.run(["lake", "build", "leancage-entry", "leancage-entry-test"], cwd=ROOT / "launch", check=True)
    subprocess.run(["lake", "build", "leancage"], cwd=ROOT / "workspace", check=True)
    # The public build and this focused check consume the same maintained helper.
    source = (ROOT / "linux/workspace.c").read_text()
    (WORK / "workspace.c").write_text(source)
    harness = (ROOT / "tests/m3/init.c").read_text()
    (WORK / "init.c").write_text(harness)
    cases = vm.CASES.CASES
    header = "static const struct testcase cases[]={\n"
    for case in cases:
        header += "{" + ",".join("." + key + "=" + (json.dumps(value, ensure_ascii=True) if isinstance(value, str) else str(value))
                                 for key, value in case.items()) + "},\n"
    (WORK / "cases.h").write_text(header + "};\n")
    compile_commands = []
    for name, path, flags in (("init", WORK / "init.c", []), ("leancage-m3-helper", WORK / "workspace.c", []),
                              ("leancage-m3-helper-test", WORK / "workspace.c", ["-DLEANCAGE_ENTRY_TEST=1"])):
        command = ["cc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-static", "-no-pie", *flags,
                   "-I", str(WORK), "-I", str(ROOT / "tests/m3"), "-I", str(ROOT / "native"),
                   "-I", str(ROOT / "linux"), str(path), "-o", str(WORK / name)]
        if name != "init":
            command[-2:-2] = [str(ROOT / "linux/entry_decimal.c"), str(ROOT / "linux/entry_handles.c"),
                              str(ROOT / "linux/process_primitives.c")]
        subprocess.run(command, check=True)
        compile_commands.append(command)
    runtime = vm.RUNTIME.load_entries()
    entries = image_entries(runtime)
    images = {"init": WORK / "init", "leancage-m3-helper": WORK / "leancage-m3-helper",
              "leancage-m3-helper-test": WORK / "leancage-m3-helper-test",
              "leancage-entry": ROOT / "launch/.lake/build/bin/leancage-entry",
              "leancage-entry-test": ROOT / "launch/.lake/build/bin/leancage-entry-test",
              "leancage": ROOT / "workspace/.lake/build/bin/leancage"}
    libraries = {library for image in (images["leancage-entry"], images["leancage"]) for library in vm.M1.dependencies(image)}
    directories = {str(p).lstrip("/") for library in libraries for p in library.parents if str(p) != "/"}
    entries[:0] = [(n, stat.S_IFDIR | 0o755, b"", 0, 0) for n in sorted(directories, key=lambda n: (n.count("/"), n))]
    entries += [(str(p).lstrip("/"), stat.S_IFREG | 0o555, p.read_bytes(), 0, 0) for p in libraries]
    entries += [(n, stat.S_IFREG | 0o555, p.read_bytes(), 0, 0) for n, p in images.items()]
    entries += [("leancage-m3-disposable-vm", stat.S_IFREG | 0o444, b"LeanCage-M3-root-VM-v1", 0, 0),
                ("dev/console", stat.S_IFCHR | 0o600, b"", 5, 1), ("dev/null", stat.S_IFCHR | 0o666, b"", 1, 3),
                ("dev/urandom", stat.S_IFCHR | 0o444, b"", 1, 9)]
    for kind, artifacts in (("trees", vm.CASES.TREES), ("blobs", vm.CASES.BLOBS)):
        entries.append(("m3-inputs/" + kind, stat.S_IFDIR | 0o700, b"", 0, 0))
        entries += [("m3-inputs/" + kind + "/" + digest, stat.S_IFREG | 0o400, data, 0, 0) for digest, data in artifacts.items()]
    # Existing harness also consumes the public Lean API after the focused native cases.
    policy = json.loads((ROOT / "profiles/offline-workspace/example-policy.json").read_text())
    policy.update(workspace_input="sha256:" + vm.CASES.input_tree, stdin_input="sha256:" + vm.CASES.stdin,
                  argv=["/usr/local/bin/python3", "-c", "import module,sys; assert module.value==42; assert sys.stdin.read()=='controlled stdin\\n'; print('api-ok')"],
                  export="regular-files")
    entries += [("api-policy.json", stat.S_IFREG | 0o400, json.dumps(policy).encode(), 0, 0),
                ("m3-assurance.json", stat.S_IFREG | 0o444, b'{}', 0, 0)]
    image = WORK / "image.cpio.gz"
    image.write_bytes(vm.M1.cpio(entries))
    if len({name for name, *_ in entries}) != len(entries):
        raise ValueError("duplicate entry prototype image path")
    files = {name: dict(mode=mode, sha256=hashlib.sha256(data).hexdigest(), major=major, minor=minor)
             for name, mode, data, major, minor in entries}
    artifacts = {name: vm.M1.sha256(p) for name, p in images.items()}
    if sources != inputs(vm):
        raise ValueError("entry route sources changed while building")
    command = vm.command_for(ROOT)
    command[command.index("-initrd") + 1] = str(image)
    process = subprocess.run(command, env=vm.environment(), capture_output=True, timeout=240)
    transcript = process.stdout.decode("utf-8", "replace").replace("\r", "")
    (WORK / "transcript.log").write_text(transcript)
    observations = vm.validate_transcript(transcript, process.returncode)
    record = dict(schema="leancage-entry-route-prototype-v2", complete_admission=False, return_code=process.returncode,
                  command=command, environment=vm.environment_record(), machine=vm.MACHINE,
                  sources=sources, artifacts=artifacts,
                  kernel_sha256=vm.M1.sha256(vm.WORK / "linux-6.18.59/arch/x86/boot/bzImage"),
                  kernel_config_sha256=vm.M1.sha256(vm.CONFIG),
                  image_sha256=hashlib.sha256(image.read_bytes()).hexdigest(), observations=observations,
                  qemu_sha256=vm.M1.sha256(Path(command[0])),
                  recorded_utc=datetime.now(timezone.utc).isoformat(),
                  generated_helper_sha256=vm.M1.sha256(WORK / "workspace.c"),
                  generated_harness_sha256=vm.M1.sha256(WORK / "init.c"),
                  compile_commands=compile_commands,
                  tools={"lean": subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT, text=True).strip(),
                         "cc": subprocess.check_output(["cc", "--version"], text=True).splitlines()[0],
                         "host": platform.freedesktop_os_release()},
                  transcript_sha256=vm.M1.sha256(WORK / "transcript.log"))
    (WORK / "evidence.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    for line in transcript.splitlines():
        if line.startswith(("M3_RESULT ", "M3_DEATH ", "M3_COMPLETE ")):
            print(line)
    if sources != inputs(vm) or artifacts != {name: vm.M1.sha256(p) for name, p in images.items()}:
        raise ValueError("entry prototype inputs changed while the VM was running")
    if record_evidence:
        TRANSCRIPT.write_bytes(gzip.compress(transcript.encode(), mtime=0))
        INVENTORY.write_bytes(gzip.compress((json.dumps(files, indent=2, sort_keys=True) + "\n").encode(), mtime=0))
        SOURCES.write_bytes(source_archive)
        record.update(transcript_archive_sha256=vm.M1.sha256(TRANSCRIPT), inventory_archive_sha256=vm.M1.sha256(INVENTORY),
                      source_archive_sha256=vm.M1.sha256(SOURCES))
        EVIDENCE.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
        check_evidence()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--record", action="store_true")
    group.add_argument("--check-evidence", action="store_true")
    args = parser.parse_args()
    if args.check_evidence:
        check_evidence()
    else:
        run(args.record)


if __name__ == "__main__":
    main()
