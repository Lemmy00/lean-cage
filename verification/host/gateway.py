#!/usr/bin/env python3
"""Build exact native host-gateway source and strict executable-Lean proof clients."""
# §AR-host-boundary.acceptance: Keep native source, ABI inputs and checked declarations together.
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
WORK = ROOT / ".tools/host/gateway"
SDK = Path("/usr/include/python3.12")


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


PROFILE = load("host_gateway_profile", "m4/bridge/profile.py")
CONNECTION = load("host_gateway_foundations", "verification/reporting/connection.py")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def flags(checker=False):
    return PROFILE.flags(checker=checker) + ["-Q", str(WORK), "HostGateway"]


def compile_file(name):
    source = HERE / (name + ".v")
    target = WORK / source.name
    if source.is_file():
        shutil.copyfile(source, target)
    try:
        result = PROFILE.run(["rocq", "c", "-q", *flags(), str(target)], cwd=WORK, timeout=120)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        target.with_suffix(".log").write_text(output)
        print(output, flush=True)
        raise
    target.with_suffix(".log").write_text(result.stdout)
    print(name + ": checked", flush=True)


def source_inputs():
    paths = []
    for source in ("host_python.c", "host_python_primitives.c"):
        dependency_output = subprocess.check_output(
            ["cc", "-M", "-I", str(SDK), str(ROOT / "linux" / source)], text=True)
        paths.extend(dependency_output.replace("\\\n", " ").split(":", 1)[1].split())
    return {path: sha(Path(path)) for path in sorted(set(paths))}


def prepare_export():
    subprocess.run(["lake", "build", "GatewayResponseWords"], cwd=ROOT / "host", check=True)
    exporter = PROFILE.WORK / "lean4export/.lake/build/bin/lean4export"
    export = WORK / "gateway-code.ndjson"
    pending = WORK / "gateway-code.pending.ndjson"
    with pending.open("w") as output:
        subprocess.run(["lake", "env", str(exporter), "GatewayResponseWords", "--",
                        "LeanCage.Host.GatewayChecks.bounded",
                        "LeanCage.Host.GatewayChecks.slotMaximum",
                        "LeanCage.Host.GatewayWords.encode",
                        "LeanCage.Host.GatewayWords.decode",
                        "LeanCage.Host.GatewayWords.Encoding",
                        "LeanCage.Host.GatewayRequestCode.Field",
                        "LeanCage.Host.GatewayRequestCode.Request",
                        "LeanCage.Host.GatewayRequestCode.magic",
                        "LeanCage.Host.GatewayRequestCode.headerPrefix",
                        "LeanCage.Host.GatewayRequestCode.descriptor",
                        "LeanCage.Host.GatewayRequestCode.encode",
                        "LeanCage.Host.GatewayResponseCode.Value",
                        "LeanCage.Host.GatewayResponseCode.Subject",
                        "LeanCage.Host.GatewayResponseCode.Encoded",
                        "LeanCage.Host.GatewayResponseCode.Encoding",
                        "LeanCage.Host.GatewayResponseCode.magic",
                        "LeanCage.Host.GatewayResponseCode.ResponseEncoding",
                        "LeanCage.Host.GatewayResponseWords.SourceEncoded",
                        "LeanCage.Host.GatewayResponseWords.SourceResponseEncoding"],
                       cwd=ROOT / "host", stdout=output, check=True)
    CONNECTION.export_records(pending)
    if export.is_file():
        previous = CONNECTION.export_fingerprints(export)
        current = CONNECTION.export_fingerprints(pending)
        changed = [name for name, value in previous.items() if current.get(name) != value]
        if changed:
            raise ValueError("gateway executable proof interface changed: " + ", ".join(changed))
    pending.replace(export)
    compile_file("GatewayImport")


def prepare():
    WORK.mkdir(parents=True, exist_ok=True)
    inputs = source_inputs()
    frontend = ROOT / ".tools/m4/CompCert/clightgen"
    command = [str(frontend), "-normalize", "-fstruct-passing", "-I", str(SDK),
               "-o", str(WORK / "GatewaySource.v"), "linux/host_python.c"]
    result = PROFILE.run(command, cwd=ROOT, profile=False, timeout=60)
    (WORK / "frontend.log").write_text(result.stdout)
    if inputs != source_inputs():
        raise ValueError("gateway C/SDK inputs changed during source translation")
    (WORK / "source-inputs.json").write_text(json.dumps(
        dict(frontend_sha256=sha(frontend), command=command, inputs=inputs),
        indent=2, sort_keys=True) + "\n")
    compile_file("GatewaySource")
    prepare_export()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("--export", action="store_true", help="refresh strict data without retranslating C")
    parser.add_argument("modules", nargs="*")
    arguments = parser.parse_args()
    if arguments.prepare:
        prepare()
    elif arguments.export:
        prepare_export()
    for name in arguments.modules:
        compile_file(name)


if __name__ == "__main__":
    main()
