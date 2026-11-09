#!/usr/bin/env python3
"""Audit the shipped core and public-library connection without changing expectations."""
# §FS-linux-product.proofs: Query actual theorem types, axioms and executable consumers.
import argparse
import copy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "assurance/product-core.json"
PREDECESSOR = ROOT / "assurance/product-core-baseline.json.gz"
PREDECESSOR_SHA256 = "8c09b326772e40479bddc3d176388bff3942e6dee0bf4fb02eb81aaed6be6df2"
PREDECESSOR_REVISION = "506337e48a2bac4fc46bb4d7bea3b88fb4f10c47"
CORE = ["LeanCageM3.validatePolicy_iff", "LeanCageM3.decodePolicy_iff", "LeanCageM3.decodePolicy_bounds",
        "LeanCageM3.Filter.policy_filter_action", "LeanCageM3.decodeResult_valid"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    paths = [ROOT / "library/LeanCageWorkspace.lean", ROOT / "library/lakefile.lean",
             ROOT / "library/lake-manifest.json", ROOT / "library/lean-toolchain", ROOT / "scripts/audit_product.py",
             ROOT / "workspace/Main.lean", ROOT / "workspace/LeanCageM3.lean"]
    paths += sorted((ROOT / "workspace/LeanCageM3").glob("*.lean"))
    paths += sorted((ROOT / "lifecycle/LeanCageM2").rglob("*.lean"))
    return {str(p.relative_to(ROOT)): sha(p) for p in paths}


def check_layout():
    layout = json.loads((ROOT / "assurance/product-layout.json").read_text())
    for name, target in (layout["aliases"] | layout["internal_header_aliases"]).items():
        alias = ROOT / name
        if not alias.is_symlink() or alias.resolve() != (ROOT / target).resolve():
            raise ValueError("layout compatibility alias differs: " + name)
    print("Product layout has one canonical implementation for every compatibility path.")


def query():
    subprocess.run(["lake", "build"], cwd=ROOT / "library", check=True)
    source = (ROOT / "scripts/m3_axiom_query.lean").read_text().replace("import LeanCageM3", "import LeanCageWorkspace")
    source += "\n#audit_module LeanCageWorkspace\n" + "".join("#audit_decl " + name + "\n" for name in CORE)
    with tempfile.TemporaryDirectory(prefix="product-query-", dir=ROOT / ".tools") as directory:
        path = Path(directory) / "Query.lean"
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "library", capture_output=True, text=True, timeout=180)
    if result.returncode:
        raise ValueError("product theorem query failed:\n" + result.stdout + result.stderr)
    records = [json.loads(line.split("LEANCAGE_AUDIT ", 1)[1]) for line in result.stdout.splitlines() if "LEANCAGE_AUDIT " in line]
    return sorted([row for row in records if "name" in row], key=lambda r: r["name"])


def predecessor():
    raw = gzip.decompress(PREDECESSOR.read_bytes())
    if hashlib.sha256(raw).hexdigest() != PREDECESSOR_SHA256:
        raise ValueError("preserved product core payload differs")
    previous = json.loads(raw)
    if previous["schema"] != "leancage-product-core-v1":
        raise ValueError("unsupported product core predecessor")
    binding = dict(archive=str(PREDECESSOR.relative_to(ROOT)), archive_sha256=sha(PREDECESSOR),
                   record_sha256=PREDECESSOR_SHA256, revision=PREDECESSOR_REVISION)
    return previous, binding


def validate_current_record(current):
    previous, binding = predecessor()
    if set(current) != set(previous) | {"predecessor"} or current["schema"] != "leancage-product-core-v2":
        raise ValueError("unsupported current product core record")
    if current["predecessor"] != binding:
        raise ValueError("product core predecessor binding differs")
    for field in set(previous) - {"schema", "source_sha256"}:
        if current[field] != previous[field]:
            raise ValueError("preserved product core field differs: " + field)


def audit(record=False, propose=False):
    check_layout()
    spec = importlib.util.spec_from_file_location("product_m1_audit", ROOT / "scripts/audit_axioms.py")
    base_audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(base_audit)
    declarations = query()
    if not declarations or not set(CORE) <= {row["name"] for row in declarations}:
        raise ValueError("missing core theorem evidence")
    previous = json.loads((ROOT / "assurance/m3-claims.json").read_text())
    preserved = [row for row in previous["declarations"] if row["name"] in CORE]
    base_audit.validate_declarations(preserved, [row for row in declarations if row["name"] in CORE])
    for row in declarations:
        if not row["is_theorem"] or set(row["axioms"]) - base_audit.LOGICAL_AXIOMS:
            raise ValueError("unreviewed product theorem/axiom: " + row["name"])
    fingerprints = sources()
    if propose:
        previous, binding = predecessor()
        base_audit.validate_declarations(previous["declarations"], declarations)
        value = copy.deepcopy(previous)
        value.update(schema="leancage-product-core-v2", predecessor=binding, source_sha256=fingerprints)
        validate_current_record(value)
        proposal = ROOT / ".tools/assurance/product-core-proposal.json"
        proposal.parent.mkdir(parents=True, exist_ok=True)
        proposal.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
        print("Current product core proposal written; exact predecessor types/axioms/claims preserved: " + str(proposal))
    elif record:
        if MANIFEST.exists():
            raise ValueError("initial recording cannot overwrite a reviewed product manifest")
        value = dict(schema="leancage-product-core-v1", spec="FS-linux-product.proofs", toolchain=(ROOT / "lean-toolchain").read_text().strip(),
                     declarations=declarations, source_sha256=fingerprints,
                     consumers={"policy": "workspace/Main.lean receives decodePolicy's validated Policy; host Workspace.validate executes the bundled controller on the same bytes; the typed library's execute checks validatePolicy before invoke",
                                "filter": "workspace/LeanCageM3/Filter.lean:bytes; build compares every byte to linux/filter.h compiled into the bundled helper",
                                "result": "workspace/LeanCageM3/API.lean:invoke calls decodeResult and detailedReport; the public library uses that identical invoke",
                                "publication": "library/LeanCageWorkspace.lean checks the actual reportStorage/detailedReport projections; verification/reporting/Reporting.lean:live_publication covers the private sender-to-decoder equation"},
                     assumptions={"logic": sorted({a for row in declarations for a in row["axioms"]}),
                                  "platform": "Compiler/runtime/FFI, Linux effects, VM/hardware and the enumerated host/native adapters in the bundle manifest remain trusted; core theorems do not prove whole-application isolation",
                                  "reporting": "Preserved conditional source and compiler statements/types/axioms are in assurance/reporting-{source,connection,compiler}.json.gz; their caller/runtime premises retain their original scope"},
                     artifact_binding="The bundle manifest identifies the compiled controller, helper, filter, checked source inputs and this exact claim record; assurance/product-vm-evidence.json identifies the executed bundle.")
        MANIFEST.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
        print("Initial product core evidence recorded; review the full declarations before handoff.")
    else:
        expected = json.loads(MANIFEST.read_text())
        if expected["schema"] == "leancage-product-core-v2":
            validate_current_record(expected)
        if expected["source_sha256"] != fingerprints or expected["toolchain"] != (ROOT / "lean-toolchain").read_text().strip():
            raise ValueError("product core inputs differ from the reviewed record")
        base_audit.validate_declarations(expected["declarations"], declarations)
        print(f"Product core audit passed: {len(declarations)} exact theorem types/axiom sets; prior core statements preserved.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--record", action="store_true", help="record the initial new product evidence once")
    parser.add_argument("--propose", action="store_true", help="propose current inputs while preserving every predecessor claim/type/axiom")
    args = parser.parse_args()
    try:
        if args.record and args.propose:
            raise ValueError("choose initial recording or a current-input proposal")
        audit(args.record, args.propose)
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print("Product audit failed: " + str(error), file=sys.stderr)
        sys.exit(1)
