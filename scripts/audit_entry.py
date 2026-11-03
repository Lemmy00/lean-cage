#!/usr/bin/env python3
"""Audit the in-progress entry implementation without upgrading the public claim."""
# §AR-entry.acceptance: Freeze exact statements and assumptions.
# Proposals never replace reviewed expectations.
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "launch"
WORK = ROOT / ".tools/launch"
MANIFEST = ROOT / "assurance/entry-claims.json"
LOGICAL = {"propext", "Classical.choice", "Quot.sound"}
SCOPE = "Conditional shared entry-body/argument proofs; native caller, provenance and complete admission remain open."


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def modules():
    result = {p.stem: p for p in (ROOT / "verification/launch").glob("*.lean")}
    result.update({str(p.relative_to(PACKAGE).with_suffix("")).replace("/", "."): p
                   for p in PACKAGE.rglob("*.lean") if ".lake" not in p.parts and p.name != "lakefile.lean"})
    return dict(sorted(result.items()))


def sources():
    paths = list(modules().values())
    paths += [ROOT / name for name in (
        "scripts/audit_entry.py", "scripts/check_entry.sh", "scripts/m3_axiom_query.lean", "launch/lakefile.lean",
        "launch/lake-manifest.json", "launch/lean-toolchain", "linux/entry_primitives.c",
        "linux/entry_handoff.h", "docs/functional-spec/FS-entry.md", "docs/architecture/AR-entry.md",
        "docs/functional-spec/FS-assurance.md", "docs/functional-spec/FS-linux-product.md",
        "docs/architecture/AR-application-verification.md",
        "docs/decisions/architectural/DA-entry-worker.md", "docs/requirements/REQ-proof-integrity.md",
        "assurance/filter-decoder.json", "assurance/m2-claims.json", "assurance/m3-claims.json")]
    # Bind the actual transitive executable definitions, rather than only the worker's own sources.
    for directory in ("LeanCage", "lifecycle", "workspace"):
        paths += [p for p in (ROOT / directory).rglob("*.lean") if ".lake" not in p.parts]
    paths += [ROOT / name for name in ("LeanCage.lean", "lean-toolchain", "lakefile.lean", "lake-manifest.json")]
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(paths))}


def query():
    shared = (ROOT / "scripts/m3_axiom_query.lean").read_text()
    declarations = "\nopen Lean Elab Command\n" + shared.split("open Lean Elab Command", 1)[1]
    # The executing definitions are part of the audit even when they are not theorems.
    definitions = ["LeanCage.Entry.admission", "LeanCage.Entry.Script.interpret",
                   "LeanCage.Entry.Worker.parse", "LeanCage.Entry.Worker.run", "main"]
    rows = []
    # Each executable owns a separate top-level main; inspect its actual import environment.
    for context, names, inspected in (
            ("production", [name for name in modules() if name != "TestMain"], definitions),
            ("test", ["TestMain"], ["main"])):
        source = "import Lean\n" + "".join(f"import {name}\n" for name in names) + declarations
        source += "".join(f"\n#audit_module {name}" for name in names)
        source += "".join(f"\n#audit_decl {name}" for name in inspected) + "\n"
        with tempfile.TemporaryDirectory(prefix="audit-", dir=WORK) as temporary:
            path = Path(temporary) / "Query.lean"
            path.write_text(source)
            run = subprocess.run(["lake", "env", "lean", str(path)], cwd=PACKAGE,
                                 capture_output=True, text=True, timeout=180)
            if run.returncode:
                raise ValueError("entry declaration query failed:\n" + run.stdout + run.stderr)
        for line in run.stdout.splitlines():
            if "LEANCAGE_AUDIT " in line:
                row = json.loads(line.split("LEANCAGE_AUDIT ", 1)[1])
                if "name" in row:
                    row["environment"] = context
                rows.append(row)
    inventory = {row["module"]: sorted(row["declarations"]) for row in rows if "module" in row}
    declarations = sorted((row for row in rows if "name" in row), key=lambda row: (row["environment"], row["name"]))
    if set(inventory) != set(modules()) or len({(r["environment"], r["name"]) for r in declarations}) != len(declarations):
        raise ValueError("entry theorem/module inventory differs or contains duplicates")
    if {name for names in inventory.values() for name in names} != {
            r["name"] for r in declarations if r["is_theorem"]}:
        raise ValueError("entry theorem inventory is incomplete")
    for row in declarations:
        row["axioms"] = sorted(row["axioms"])
        if set(row["axioms"]) - LOGICAL:
            raise ValueError("forbidden transitive axiom: " + row["name"])
    return inventory, declarations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--propose", action="store_true", help="write an ignored proposal for statement review")
    args = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    before = sources()
    expected = None if args.propose else json.loads(MANIFEST.read_text())
    if expected is not None and expected["source_sha256"] != before:
        raise ValueError("entry sources changed; review the changed statements before amending the manifest")
    subprocess.run(["lake", "build", "LeanCageEntry", "EntryVerification", "leancage-entry", "leancage-entry-test"],
                   cwd=PACKAGE, check=True)
    inventory, declarations = query()
    record = dict(schema="leancage-entry-partial-claims-v1", complete_admission=False, scope=SCOPE,
                  toolchain=(PACKAGE / "lean-toolchain").read_text().strip(),
                  modules=inventory, declarations=declarations, source_sha256=before)
    if sources() != before:
        raise ValueError("entry sources changed during the audit")
    if args.propose:
        path = WORK / "proposed-entry-claims.json"
        path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
        print("Entry statement proposal written for review: " + str(path))
        return
    if record != expected:
        raise ValueError("entry statements, module inventory or transitive assumptions differ")
    artifacts = {str(p.relative_to(ROOT)): sha(p) for p in (PACKAGE / ".lake/build").rglob("*")
                 if p.is_file() and p.suffix in {".olean", ".a"}}
    for name in ("leancage-entry", "leancage-entry-test"):
        p = PACKAGE / ".lake/build/bin" / name
        artifacts[str(p.relative_to(ROOT))] = sha(p)
    (WORK / "audit.json").write_text(json.dumps(dict(manifest_sha256=sha(MANIFEST),
        sources=before, checked_artifacts=artifacts), indent=2, sort_keys=True) + "\n")
    print("Entry statement/axiom audit passed; scope remains conditional entry body and argument binding.")


if __name__ == "__main__":
    main()
