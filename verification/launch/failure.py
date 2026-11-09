#!/usr/bin/env python3
"""Replay accepted local failure paths against the complete current helper."""
# §AR-entry.caller: Source reuse checks actual functions and environment, not only file hashes.
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / ".tools/launch/failure"
RECORD = ROOT / "assurance/entry-failure.json.gz"
SOURCE_MODULES = ("NativeHandoffMachine", "NativeHandoffContexts", "HandoffRegion",
                  "NativeHandoffError", "NativeHandoffNumberBound")
FAILURE_MODULES = ("FailureSource", "FailureMemory", "FailureBranches", "FailureProgress", "FailureMachine")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def sources():
    native = load("failure_native_inputs", "verification/launch/process.py").native_sources()
    paths = native | {ROOT / "verification/launch" / (name + ".v") for name in (
        *SOURCE_MODULES, "FailureProgress", "FailureMachine")}
    paths.update(ROOT / "m4/connection" / (name + ".v") for name in FAILURE_MODULES[:3])
    paths.update(ROOT / name for name in (
        "verification/launch/failure.py", "verification/launch/process.py", "m4/bridge/profile.py",
        "m4/bridge/toolchain-lock.json", "m4/bridge/strict-importer.patch",
        "verification/reporting/connection.py", "assurance/reporting-source.json.gz",
        "docs/functional-spec/FS-entry.md", "docs/architecture/AR-entry.md"))
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(paths)}


def predecessors():
    accepted = json.loads(gzip.decompress((ROOT / "assurance/reporting-source.json.gz").read_bytes()))
    frontend = ROOT / ".tools/m4/CompCert/clightgen"
    if sha(frontend) != accepted["dependency_sha256"][str(frontend.relative_to(ROOT))]:
        raise ValueError("failure source frontend differs from the accepted profile")
    dependencies = {name: digest for name, digest in accepted["dependency_sha256"].items()
                    if name.startswith(".tools/m4/bridge/") and name.endswith(".vo")}
    dependencies.update({".tools/reporting/rebase/" + name: digest
                         for name, digest in accepted["cache_sha256"].items()
                         if name.startswith("main/number/") or name == "main/proofs/Main.vo"})
    for name, digest in dependencies.items():
        if sha(ROOT / name) != digest:
            raise ValueError("preserved failure proof dependency differs: " + name)
    return dependencies


def profile():
    spec = importlib.util.spec_from_file_location("entry_failure_profile", ROOT / "m4/bridge/profile.py")
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def flags(p, checker=False):
    return p.flags(checker=checker) + ["-Q", str(WORK / "source"), "EntryNative",
                                     "-Q", str(WORK / "proofs"), "EntryFailure",
                                     "-Q", str(ROOT / ".tools/reporting/rebase/main/proofs"), "LeanCageMain",
                                     "-Q", str(ROOT / ".tools/reporting/rebase/main/number"), "LeanCageMainNumber"]


def prepare():
    p = profile()
    for directory in (WORK / "source", WORK / "proofs"):
        directory.mkdir(parents=True, exist_ok=True)
    p.run([str(ROOT / ".tools/m4/CompCert/clightgen"), "-normalize", "-fstruct-passing",
           "-I", "native", "-I", "linux", "-o", str(WORK / "source/EntrySource.v"),
           "linux/workspace.c"], cwd=ROOT, profile=False, timeout=60)
    # Replaying these proofs under the real current global environment checks all
    # symbol resolutions. The changed production fault implementation is proved
    # separately; the old selector theorem is deliberately not reused.
    for name in ("FailureSource", "FailureMemory", "FailureBranches"):
        text = (ROOT / "m4/connection" / (name + ".v")).read_text()
        text = text.replace("Slice.prog", "EntrySource.prog")
        text = text.replace("FailureSourceDraft", "EntryFailure.FailureSource")
        text = text.replace("FailureMemoryDraft", "EntryFailure.FailureMemory")
        text = text.replace("Import ListNotations.", "From EntryNative Require Import EntrySource.\nImport ListNotations.", 1)
        (WORK / "proofs" / (name + ".v")).write_text(text)
    for name in ("FailureProgress", "FailureMachine"):
        (WORK / "proofs" / (name + ".v")).write_bytes((ROOT / "verification/launch" / (name + ".v")).read_bytes())
    (WORK / "source/NativeHandoffMachine.v").write_bytes((ROOT / "verification/launch/NativeHandoffMachine.v").read_bytes())
    (WORK / "source/NativeHandoffContexts.v").write_bytes((ROOT / "verification/launch/NativeHandoffContexts.v").read_bytes())
    (WORK / "source/HandoffRegion.v").write_bytes((ROOT / "verification/launch/HandoffRegion.v").read_bytes())
    (WORK / "source/NativeHandoffError.v").write_bytes((ROOT / "verification/launch/NativeHandoffError.v").read_bytes())
    (WORK / "source/NativeHandoffNumberBound.v").write_bytes((ROOT / "verification/launch/NativeHandoffNumberBound.v").read_bytes())
    for path in [WORK / "source/EntrySource.v", WORK / "source/NativeHandoffMachine.v",
                 WORK / "source/NativeHandoffContexts.v", WORK / "source/HandoffRegion.v",
                 WORK / "source/NativeHandoffError.v",
                 WORK / "source/NativeHandoffNumberBound.v",
                 *(WORK / "proofs" / (name + ".v") for name in (
                     "FailureSource", "FailureMemory", "FailureBranches", "FailureProgress", "FailureMachine"))]:
        try:
            result = p.run(["rocq", "c", "-q", *flags(p), str(path)], cwd=WORK, timeout=120)
        except subprocess.CalledProcessError as error:
            print(error.stdout)
            raise
        (path.with_suffix(".log")).write_text(result.stdout)
        print("Checked " + path.name, flush=True)


def collect():
    before = sources()
    p = profile()
    p.verify_tools()
    dependencies = predecessors()
    prepare()
    names = []
    for namespace, directory, modules in (("EntryNative", WORK / "source", SOURCE_MODULES),
                                           ("EntryFailure", WORK / "proofs", FAILURE_MODULES)):
        for module in modules:
            names += [namespace + "." + module + "." + name for name in re.findall(
                r'^(?:Theorem|Lemma)\s+(\w+)\b', (directory / (module + ".v")).read_text(), re.M)]
    roots = ["EntryNative." + name for name in SOURCE_MODULES] + ["EntryFailure." + name for name in FAILURE_MODULES]
    query = ["Require Import " + " ".join(roots) + ".", "Set Printing Depth 10000."]
    for index, name in enumerate(names):
        query += [f'Redirect "type-{index}" Check {name}.', f'Redirect "axioms-{index}" Print Assumptions {name}.']
    audit = WORK / "Audit.v"
    audit.write_text("\n".join(query) + "\n")
    p.run(["rocq", "c", "-q", *flags(p), str(audit)], cwd=WORK, timeout=120)
    foundations = load("failure_foundations", "verification/reporting/connection.py")
    declarations = []
    for index, name in enumerate(names):
        assumptions = (WORK / f"axioms-{index}.out").read_text().strip()
        parameters, uip = foundations.foundations(assumptions)
        declarations.append(dict(name=name, type=(WORK / f"type-{index}.out").read_text().strip(),
                                 assumptions=assumptions, assumption_names=parameters, definitional_uip=uip))
    checked = p.run(["rocq", "check", "-silent", *flags(p, checker=True), *roots], cwd=WORK, timeout=240)
    (WORK / "kernel-check.log").write_text(checked.stdout)
    if sources() != before:
        raise ValueError("failure proof inputs changed during kernel checking")
    artifacts = {str(path.relative_to(WORK)): sha(path) for directory in (WORK / "source", WORK / "proofs")
                 for path in directory.iterdir() if path.suffix in {".v", ".vo"}}
    artifacts.update({"Audit.v": sha(audit), "Audit.vo": sha(audit.with_suffix(".vo"))})
    record = dict(schema="leancage-entry-failure-source-v1", complete_admission=False,
                  scope="Actual production failure source, caller continuations and no-image safety; source-region and numeric/errno composition adapters. Full admission is composed separately.",
                  sources=before, preserved_dependencies=dependencies, declarations=declarations,
                  artifacts=artifacts, kernel_roots=roots, kernel_log_sha256=sha(WORK / "kernel-check.log"))
    (WORK / "proposal.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    return record


def check():
    expected = json.loads(gzip.decompress(RECORD.read_bytes()))
    if expected["sources"] != sources() or expected["preserved_dependencies"] != predecessors():
        raise ValueError("reviewed failure source/dependency inputs differ")
    profile().verify_tools()
    if all((WORK / name).is_file() and sha(WORK / name) == digest
           for name, digest in expected["artifacts"].items()):
        print("Current failure source/assumption bindings checked; matching kernel artifacts reused.")
    elif collect() != expected:
        raise ValueError("current failure source statements, foundations or artifacts differ")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--compile", action="store_true", help="focused source proof compilation during development")
    mode.add_argument("--propose", action="store_true", help="kernel-check and write an ignored statement proposal")
    args = parser.parse_args()
    if args.compile:
        prepare()
    elif args.propose:
        collect()
        print("Failure source/type/foundations proposal written: " + str(WORK / "proposal.json"))
    else:
        check()
