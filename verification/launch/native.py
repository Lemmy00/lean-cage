#!/usr/bin/env python3
"""Check the native numeric/value connection, retaining the remaining handoff obligations."""
# §AR-entry.caller: The source-function proof is separate from its caller/precondition producer.
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path(__file__).resolve().parent
WORK = ROOT / ".tools/launch/source"
RECORD = ROOT / "assurance/entry-native-values.json.gz"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


PROFILE = load("entry_native_profile", "m4/bridge/profile.py")
FOUNDATIONS = load("entry_native_foundations", "verification/reporting/connection.py")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    return {name: sha(ROOT / name) for name in (
        "verification/launch/native.py", "verification/launch/NativeArguments.v",
        "verification/launch/NativeValues.v", "assurance/entry-route-vm.json",
        "assurance/entry-arguments.json.gz", "assurance/reporting-source.json.gz",
        "m4/bridge/profile.py", "m4/bridge/toolchain-lock.json", "m4/bridge/strict-importer.patch")}


def flags(checker=False):
    return PROFILE.flags(checker=checker) + [
        "-Q", str(ROOT / ".tools/launch/arguments"), "", "-Q", str(WORK), "EntryNative",
        "-Q", str(ROOT / ".tools/reporting/rebase/main/proofs"), "LeanCageMain",
        "-Q", str(ROOT / ".tools/reporting/rebase/main/number"), "LeanCageMainNumber"]


def build(helper):
    WORK.mkdir(parents=True, exist_ok=True)
    before = sources()
    route = json.loads((ROOT / "assurance/entry-route-vm.json").read_text())
    if hashlib.sha256(helper.encode()).hexdigest() != route["generated_helper_sha256"]:
        raise ValueError("native source differs from the source compiled for the route VM")
    load("entry_native_vm_record", "tests/entry/prototype.py").check_evidence()
    subprocess.run(["python3", "verification/launch/arguments.py"], cwd=ROOT, check=True)
    PROFILE.verify_tools()
    accepted = json.loads(gzip.decompress((ROOT / "assurance/reporting-source.json.gz").read_bytes()))
    frontend = ROOT / ".tools/m4/CompCert/clightgen"
    if sha(frontend) != accepted["dependency_sha256"][".tools/m4/CompCert/clightgen"]:
        raise ValueError("native frontend differs from the accepted source proof profile")
    inherited = {name: digest for name, digest in accepted["cache_sha256"].items()
                 if name.startswith("main/number/") or name == "main/proofs/Main.vo"}
    for name, digest in inherited.items():
        if sha(ROOT / ".tools/reporting/rebase" / name) != digest:
            raise ValueError("reused accepted numeric proof input differs: " + name)
    (WORK / "workspace.c").write_text(helper)
    command = [str(frontend), "-normalize", "-fstruct-passing", "-I", "native", "-I", "linux",
               "-o", ".tools/launch/source/EntrySource.v", ".tools/launch/source/workspace.c"]
    PROFILE.run(command, cwd=ROOT, profile=False, timeout=60)
    for name in ("NativeArguments", "NativeValues"):
        (WORK / (name + ".v")).write_bytes((DIRECTORY / (name + ".v")).read_bytes())
    for name in ("EntrySource", "NativeArguments", "NativeValues"):
        path = WORK / (name + ".v")
        try:
            result = PROFILE.run(["rocq", "c", "-q", *flags(), str(path)], cwd=WORK, timeout=90)
        except subprocess.CalledProcessError as error:
            (WORK / (name + ".log")).write_text(error.stdout)
            raise
        (WORK / (name + ".log")).write_text(result.stdout)
    names = ["EntryNative.NativeArguments.current_entry_number_exact",
             "EntryNative.NativeArguments.current_entry_number_value",
             "EntryNative.NativeValues.argument_byte_exact", "EntryNative.NativeValues.argument_fold_native",
             "EntryNative.NativeValues.current_number_worker_value"]
    query = ["From EntryNative Require Import NativeArguments NativeValues.", "Set Printing Depth 10000."]
    for index, name in enumerate(names):
        query += [f'Redirect "native-type-{index}" Check {name}.',
                  f'Redirect "native-assumptions-{index}" Print Assumptions {name}.']
    audit = WORK / "Audit.v"
    audit.write_text("\n".join(query) + "\n")
    PROFILE.run(["rocq", "c", "-q", *flags(), str(audit)], cwd=WORK, timeout=60)
    declarations = []
    for index, name in enumerate(names):
        assumptions = (WORK / f"native-assumptions-{index}.out").read_text().strip()
        axioms, uip = FOUNDATIONS.foundations(assumptions)
        declarations.append(dict(name=name, type=(WORK / f"native-type-{index}.out").read_text().strip(),
                                 assumptions=assumptions, assumption_names=axioms, definitional_uip=uip))
    checked = PROFILE.run(["rocq", "check", "-silent", *flags(checker=True),
                           "EntryNative.NativeArguments", "EntryNative.NativeValues"], cwd=WORK, timeout=180)
    (WORK / "kernel-check.log").write_text(checked.stdout)
    if before != sources():
        raise ValueError("native connection inputs changed during checking")
    artifacts = {name: sha(WORK / name) for name in (
        "workspace.c", "EntrySource.v", "EntrySource.vo", "NativeArguments.v", "NativeArguments.vo",
        "NativeValues.v", "NativeValues.vo", "Audit.v", "Audit.vo")}
    record = dict(schema="leancage-entry-native-value-interface-v1", complete_admission=False,
                  scope="Actual numeric callee and ordinary worker-byte value agreement; guest handoff/handshake remain open.",
                  source_sha256=before, helper_c_source=helper, frontend_sha256=sha(frontend),
                  reused_numeric_cache=inherited, declarations=declarations, artifacts=artifacts)
    (WORK / "proposal.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--propose", action="store_true")
    args = parser.parse_args()
    if args.propose:
        helper = (ROOT / ".tools/launch/prototype/workspace.c").read_text()
        build(helper)
        print("Native value connection proposal written: " + str(WORK / "proposal.json"))
        return
    expected = json.loads(gzip.decompress(RECORD.read_bytes()))
    load("entry_native_current_vm_inputs", "tests/entry/prototype.py").check_evidence()
    subprocess.run(["python3", "verification/launch/arguments.py"], cwd=ROOT, check=True)
    PROFILE.verify_tools()
    if expected["source_sha256"] != sources():
        raise ValueError("reviewed native value connection inputs differ")
    if all((WORK / name).is_file() and sha(WORK / name) == digest for name, digest in expected["artifacts"].items()):
        print("Native numeric/value connection checked: matching kernel-checked artifacts reused.")
    elif build(expected["helper_c_source"]) != expected:
        raise ValueError("native connection replay differs from the reviewed record")
    else:
        print("Native numeric/value connection replay passed; complete handoff/handshake remain open.")


if __name__ == "__main__":
    main()
