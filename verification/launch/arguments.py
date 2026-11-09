#!/usr/bin/env python3
"""Check the narrow argument-byte proof interface; native argument binding remains separate."""
# §AR-entry.caller: Import computation strictly and check the exact bound proposition in Rocq.
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path(__file__).resolve().parent
WORK = ROOT / ".tools/launch/arguments"
RECORD = ROOT / "assurance/entry-arguments.json.gz"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


PROFILE = load("entry_argument_profile", "m4/bridge/profile.py")
CONNECTION = load("entry_argument_foundations", "verification/reporting/connection.py")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    return {name: sha(ROOT / name) for name in (
        "verification/launch/arguments.py", "verification/launch/ArgumentsImport.v",
        "verification/launch/ArgumentConnection.v", "verification/launch/ArgumentValues.v",
        "verification/launch/WorkerConnection.lean", "launch/LeanCageEntry/Arguments.lean",
        "launch/lean-toolchain", "launch/lake-manifest.json", "launch/lakefile.lean",
        "m4/bridge/profile.py", "m4/bridge/toolchain-lock.json", "m4/bridge/strict-importer.patch",
        "verification/reporting/connection.py", "assurance/m4-bridge-claims.json")}


def flags(checker=False):
    return PROFILE.flags(checker=checker) + ["-Q", str(WORK), ""]


def build():
    before = sources()
    WORK.mkdir(parents=True, exist_ok=True)
    PROFILE.verify_tools()
    subprocess.run(["lake", "-d", "launch", "build", "WorkerConnection"], cwd=ROOT, check=True)
    exporter = PROFILE.WORK / "lean4export/.lake/build/bin/lean4export"
    export = WORK / "arguments-code.ndjson"
    with export.open("w") as out:
        subprocess.run(["lake", "-d", "launch", "env", str(exporter), "WorkerConnection",
                        "--", "LeanCage.Entry.Arguments.unsigned", "LeanCage.Entry.ArgumentMeaning.decimalValue",
                        "LeanCage.Entry.ArgumentMeaning.byteValues", "LeanCage.Entry.ArgumentMeaning.nativeValues",
                        "LeanCage.Entry.PhysicalHandoff.binding", "LeanCage.Entry.PhysicalHandoff.objectCode",
                        "LeanCage.Entry.PhysicalHandoff.grantBeforeRead"],
                       cwd=ROOT, stdout=out, check=True)
    # Reject exported axioms before invoking the pinned, strict importer.
    CONNECTION.export_records(export)
    for name in ("ArgumentsImport", "ArgumentConnection", "ArgumentValues"):
        path = WORK / (name + ".v")
        shutil.copyfile(DIRECTORY / path.name, path)
        try:
            run = PROFILE.run(["rocq", "c", "-q", *flags(), str(path)], cwd=WORK, timeout=90)
        except subprocess.CalledProcessError as error:
            (WORK / (name + ".log")).write_text(error.stdout)
            raise
        (WORK / (name + ".log")).write_text(run.stdout)
    names = ["ArgumentConnection.imported_unsigned_bound", "ArgumentConnection.unsigned_bound_checked_type",
             "ArgumentValues.argument_unsigned_value", "ArgumentValues.imported_unsigned_value",
             "ArgumentsImport.LeanCage_Entry_ArgumentMeaning_byteValues",
             "ArgumentsImport.LeanCage_Entry_ArgumentMeaning_nativeValues",
             "ArgumentsImport.LeanCage_Entry_PhysicalHandoff_binding",
             "ArgumentsImport.LeanCage_Entry_PhysicalHandoff_objectCode",
             "ArgumentsImport.LeanCage_Entry_PhysicalHandoff_grantBeforeRead"]
    query = ["From LeanImport Require Import Lean.", "Require Import ArgumentConnection ArgumentValues."]
    for index, name in enumerate(names):
        query += [f'Redirect "type-{index}" Check {name}.',
                  f'Redirect "assumptions-{index}" Print Assumptions {name}.']
    path = WORK / "Audit.v"
    path.write_text("\n".join(query) + "\n")
    PROFILE.run(["rocq", "c", "-q", *flags(), str(path)], cwd=WORK, timeout=60)
    declarations = []
    for index, name in enumerate(names):
        assumptions = (WORK / f"assumptions-{index}.out").read_text().strip()
        axioms, uip = CONNECTION.foundations(assumptions)
        declarations.append(dict(name=name, type=(WORK / f"type-{index}.out").read_text().strip(),
                                 assumptions=assumptions, assumption_names=axioms, definitional_uip=uip))
    checked = PROFILE.run(["rocq", "check", "-silent", *flags(checker=True),
                           "ArgumentsImport", "ArgumentConnection", "ArgumentValues"], cwd=WORK, timeout=120)
    (WORK / "kernel-check.log").write_text(checked.stdout)
    if before != sources():
        raise ValueError("argument interface inputs changed during checking")
    artifacts = {name: sha(WORK / name) for name in (
        "ArgumentsImport.v", "ArgumentsImport.vo", "ArgumentConnection.v", "ArgumentConnection.vo",
        "ArgumentValues.v", "ArgumentValues.vo", "Audit.v", "Audit.vo", "arguments-code.ndjson")}
    record = dict(schema="leancage-entry-argument-interface-v1", complete_native_binding=False,
                  scope="Strict actual byte computation, bounds and positional meaning; no C argv-memory/caller proof.",
                  source_sha256=before, declarations=declarations, artifacts=artifacts,
                  export_fingerprints=CONNECTION.export_fingerprints(export),
                  toolchain=PROFILE.lock())
    (WORK / "proposal.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--propose", action="store_true")
    args = parser.parse_args()
    PROFILE.verify_tools()
    expected = None if args.propose else json.loads(gzip.decompress(RECORD.read_bytes()))
    if expected is not None and expected["source_sha256"] != sources():
        raise ValueError("reviewed argument interface inputs differ")
    # A matching checked artifact is reused; missing/different artifacts require replay.
    if expected is not None and all((WORK / n).is_file() and sha(WORK / n) == digest
                                    for n, digest in expected["artifacts"].items()):
        print("Strict argument interface checked: matching kernel-checked artifacts reused.")
        return
    actual = build()
    if args.propose:
        print("Strict argument interface proposal written: " + str(WORK / "proposal.json"))
    elif actual != expected:
        raise ValueError("argument proof/type/foundation evidence differs")
    else:
        print("Strict argument interface replay passed; native argument binding remains open.")


if __name__ == "__main__":
    main()
