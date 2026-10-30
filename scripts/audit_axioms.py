#!/usr/bin/env python3
"""Build and audit M1 theorem evidence, preserving the reviewed M1.2 decoder claims."""

# §AR-filter-decoder.audit: Declaration/type/axiom checks supplement kernel checking.

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


PROJECT = Path(__file__).resolve().parents[1]
MANIFEST = PROJECT / "assurance/filter-decoder.json"
BASELINE = PROJECT / "assurance/m1.2-decoder-claims.json"
QUERY = PROJECT / "scripts/axiom_query.lean"
LOGICAL_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")
# §AR-filter-decoder.audit: Bound complete queries while accommodating shared CI runner speed.
QUERY_TIMEOUT_SECONDS = 180


class AuditError(ValueError):
    pass


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def project_modules():
    paths = [PROJECT / "LeanCage.lean", *sorted((PROJECT / "LeanCage").rglob("*.lean"))]
    return {str(path.relative_to(PROJECT).with_suffix("")).replace("/", "."): path
            for path in paths}


def required_sources():
    paths = list(project_modules().values()) + [
        PROJECT / name for name in (
            "lean-toolchain", "lake-manifest.json", "lakefile.lean", "M1Main.lean",
            "scripts/axiom_query.lean", "scripts/audit_axioms.py",
            "scripts/check.sh", "scripts/run_m1_vm.py", "native/leancage_m1.c",
            "assurance/m1.2-decoder-claims.json",
            "assurance/m1-vm-evidence.json", "assurance/m1-vm-transcript.log",
            "tests/vm/bootstrap-pins.json", "tests/vm/kernel.fragment",
            "tests/vm/linux-6.18.59.config", "tests/vm/init.c", "tests/vm/guest.c",
            "docs/functional-spec/FS-filter-loading.md",
            "docs/functional-spec/FS-assurance.md",
            "docs/requirements/REQ-proof-integrity.md",
            "docs/architecture/AR-filter-decoder.md",
            "docs/architecture/AR-m1-launch.md", "docs/architecture/AR-filter-slice.md",
            "docs/decisions/architectural/DA-m1-filter-profile.md",
        )
    ]
    paths += sorted((PROJECT / "tests/integration").glob("*.lean"))
    paths += sorted((PROJECT / "tests/integration").glob("test_*.py"))
    return {str(path.relative_to(PROJECT)): sha256(path) for path in paths}


def query_environment(modules=(), declarations=(), extra_source=""):
    for name in [*modules, *declarations]:
        if not NAME.fullmatch(name):
            raise AuditError(f"Invalid Lean name: {name!r}")
    source = QUERY.read_text() + "\n" + extra_source + "\n"
    source += "".join(f"#audit_module {name}\n" for name in modules)
    source += "".join(f"#audit_decl {name}\n" for name in declarations)
    cache = PROJECT / ".tools/assurance"
    cache.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="query-", dir=cache) as directory:
        probe = Path(directory) / "Query.lean"
        probe.write_text(source)
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)], cwd=PROJECT,
            capture_output=True, text=True, timeout=QUERY_TIMEOUT_SECONDS,
        )
    if result.returncode:
        raise AuditError("Lean audit query failed:\n" + result.stdout + result.stderr)
    records = []
    for line in result.stdout.splitlines():
        if "LEANCAGE_AUDIT " in line:
            records.append(json.loads(line.split("LEANCAGE_AUDIT ", 1)[1]))
    if not records:
        raise AuditError("Lean audit query returned no evidence")
    return records


def normalized_type(text):
    return " ".join(text.split())


def validate_declarations(expected, actual):
    expected_names = [item["name"] for item in expected]
    actual_names = [item["name"] for item in actual]
    if len(set(expected_names)) != len(expected_names):
        raise AuditError("Duplicate declaration in manifest")
    if len(set(actual_names)) != len(actual_names):
        raise AuditError("Duplicate declaration in Lean evidence")
    if not expected_names or set(expected_names) != set(actual_names):
        raise AuditError("Theorem inventory differs from the reviewed manifest")
    expected_by_name = {item["name"]: item for item in expected}
    for record in actual:
        name = record["name"]
        claim = expected_by_name[name]
        if not record["is_theorem"]:
            raise AuditError(f"Not a theorem: {name}")
        forbidden = set(record["axioms"]) - LOGICAL_AXIOMS
        if forbidden:
            raise AuditError(f"Forbidden transitive axioms for {name}: {sorted(forbidden)}")
        if normalized_type(record["type"]) != normalized_type(claim["type"]):
            raise AuditError(f"Theorem type differs: {name}")
        if set(record["axioms"]) != set(claim["axioms"]):
            raise AuditError(f"Unreviewed axiom set: {name}")


def audit():
    manifest_hash = sha256(MANIFEST)
    manifest = json.loads(MANIFEST.read_text())
    if manifest["schema_version"] != 1:
        raise AuditError("Unsupported assurance manifest version")
    modules = project_modules()
    if set(manifest["modules"]) != set(modules):
        raise AuditError("Project module inventory differs from the manifest")
    source_hashes = required_sources()
    if manifest["source_sha256"] != source_hashes:
        raise AuditError("Source/dependency identities differ from the reviewed manifest")
    if manifest["toolchain"] != (PROJECT / "lean-toolchain").read_text().strip():
        raise AuditError("Toolchain pin differs from the manifest")
    subprocess.run(["lake", "build"], cwd=PROJECT, check=True)
    records = query_environment(modules=sorted(modules))
    inventories = [item for item in records if "module" in item]
    if {item["module"] for item in inventories} != set(modules):
        raise AuditError("Missing module inventory in Lean evidence")
    declarations = [item for item in records if "name" in item]
    inventoried = [name for item in inventories for name in item["declarations"]]
    if sorted(inventoried) != sorted(item["name"] for item in declarations):
        raise AuditError("Missing declaration evidence")
    validate_declarations(manifest["declarations"], declarations)
    baseline = json.loads(BASELINE.read_text())
    baseline_names = {item["name"] for item in baseline["declarations"]}
    validate_declarations(baseline["declarations"],
                          [item for item in declarations if item["name"] in baseline_names])
    claims = manifest["claims"]
    if (not claims or len(set(claims)) != len(claims)
            or not set(claims) <= {item["name"] for item in declarations}):
        raise AuditError("Missing, duplicate, or non-theorem named security claim")
    if required_sources() != source_hashes or sha256(MANIFEST) != manifest_hash:
        raise AuditError("Sources or reviewed manifest changed during audit")
    artifacts = {}
    for module in modules:
        base = PROJECT / ".lake/build/lib/lean" / module.replace(".", "/")
        olean = base.with_suffix(".olean")
        if not olean.is_file():
            raise AuditError(f"Missing checked Lean artifact: {module}")
        for suffix in (".olean", ".olean.private", ".olean.server"):
            path = base.with_suffix(suffix)
            if path.is_file():
                artifacts[str(path.relative_to(PROJECT))] = sha256(path)
    version = subprocess.check_output(
        ["lake", "env", "lean", "--version"], cwd=PROJECT, text=True,
    ).strip()
    report = {
        "schema_version": 1, "scope": manifest["scope"],
        "manifest_sha256": sha256(MANIFEST), "source_sha256": source_hashes,
        "lean_version": version, "artifacts_sha256": artifacts,
        "declarations": sorted(declarations, key=lambda item: item["name"]),
        "kernel_runtime_and_ffi": "Not certified by theorem audit; separately tested VM evidence remains conditional on native/Linux correspondence",
    }
    output = PROJECT / ".tools/assurance/filter-decoder-report.json"
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"Axiom audit passed: {len(declarations)} theorem declarations; "
          f"types, axiom sets, and {len(source_hashes)} source/dependency identities match.")
    print(f"Checked Lean artifact identities: {output.relative_to(PROJECT)}")


if __name__ == "__main__":
    try:
        audit()
    except (AuditError, KeyError, OSError, subprocess.SubprocessError, json.JSONDecodeError) as error:
        print(f"Axiom audit failed: {error}", file=sys.stderr)
        sys.exit(1)
