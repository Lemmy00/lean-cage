#!/usr/bin/env python3
"""Amend operational status fingerprints while freezing every original proof field."""
# §AR-workspace-vm.migration: Preserve original types, axioms, source proofs and cache identities.
import argparse
import base64
import copy
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "d44c96139da45d750e079da2007928d1bddb531b"
RECORD = ROOT / "assurance/product-evidence-migration.json"
CACHE_ARCHIVE = ROOT / "assurance/product-cache-baseline.json.gz"
CACHE_ARCHIVE_SHA256 = "5c31d32c9d26a8f060f1743ee1c337e79234e5194e393cff68b5367c2b882372"
CACHE_RECORD = "assurance/reporting-compiler.json.gz"
CACHE_INPUTS = {
    "m3/.lake/build/lib/lean/LeanCageM3/API.olean":
        "ebde2ab2cdaee551d5589a39b63673b810b102938932e46bdb71c3a00ae2af20",
    "m3/.lake/build/lib/lean/Main.olean":
        "6d3bc00f03a400c141acb7816953e82a06f55e735a8937e02d2c6639e477c2da",
}
FILES = ["assurance/filter-decoder.json", "assurance/m2-claims.json", "assurance/m3-claims.json",
         "assurance/reporting-source.json.gz", "assurance/reporting-connection.json.gz",
         "assurance/reporting-compiler.json.gz"]
OPERATIONAL_CHECKER = "verification/compiler/amendment.py"
OPERATIONAL_CONSUMERS = {"verification/reporting/connection.py", "verification/compiler/check.py"}
GATE = "scripts/check.sh"
ALLOWED = {"docs/functional-spec/FS-assurance.md", OPERATIONAL_CHECKER, GATE, *FILES, *OPERATIONAL_CONSUMERS}
GROUPS = ("source_sha256", "inputs_sha256")
# These are historical bindings, never substitutions in the current workspace gate.
HISTORICAL = {"native/leancage_m3.c", "linux/workspace.c", "scripts/run_m3_vm.py",
              "scripts/audit_m3.py", "tests/m3/init.c", "verification/reporting/source.py",
              "verification/reporting/check.py", "verification/reporting/README.md",
              "m3/tests/integration/test_evidence.py", "m3/LeanCageM3/API.lean",
              "m3/lakefile.lean", "tests/m3/cases.py", "tests/reporting/capture.c"}
GATE_BEFORE = "cc -std=c11 -O2 -Wall -Wextra -Werror -static -no-pie native/leancage_m3.c \\\n"
GATE_AFTER = ("cc -std=c11 -O2 -Wall -Wextra -Werror -static -no-pie -I linux native/leancage_m3.c \\\n"
              "  linux/entry_decimal.c linux/entry_handles.c linux/process_primitives.c \\\n")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def decode(name, raw):
    return json.loads(gzip.decompress(raw) if name.endswith(".gz") else raw)


def encode(name, value):
    data = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    return gzip.compress(data, mtime=0) if name.endswith(".gz") else data


def preserved_inputs():
    import importlib.util
    spec = importlib.util.spec_from_file_location("migration_workspace_predecessor", ROOT / "scripts/workspace_evidence.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.read_baseline(), module.binding()


def original_record(name):
    raw = subprocess.run(["git", "show", BASELINE + ":" + name], cwd=ROOT,
                         check=True, capture_output=True).stdout
    return raw, decode(name, raw)


def preserved_caches():
    """Read exact accepted compiled bytes; never substitute today's rebuilt cache."""
    raw = CACHE_ARCHIVE.read_bytes()
    if sha(raw) != CACHE_ARCHIVE_SHA256:
        raise ValueError("sealed compiled predecessor archive differs")
    record = json.loads(gzip.decompress(raw))
    if (set(record) != {"schema", "baseline_commit", "baseline_record", "files"}
            or record["schema"] != "leancage-product-cache-baseline-v1"
            or record["baseline_commit"] != BASELINE or record["baseline_record"] != CACHE_RECORD
            or set(record["files"]) != set(CACHE_INPUTS)):
        raise ValueError("compiled predecessor schema/revision/inventory differs")
    _, baseline = original_record(CACHE_RECORD)
    files = {}
    for name, expected in CACHE_INPUTS.items():
        entry = record["files"][name]
        if set(entry) != {"sha256", "base64"}:
            raise ValueError("compiled predecessor entry differs: " + name)
        data = base64.b64decode(entry["base64"], validate=True)
        if sha(data) != expected or entry["sha256"] != expected or baseline["inputs_sha256"].get(name) != expected:
            raise ValueError("compiled predecessor bytes/baseline identity differs: " + name)
        files[name] = data
    return files, dict(archive=str(CACHE_ARCHIVE.relative_to(ROOT)), archive_sha256=sha(raw),
                       baseline_commit=BASELINE, baseline_record=CACHE_RECORD, files_sha256=CACHE_INPUTS)


def current_fingerprints(name, original, preserved, caches, historical, historical_caches):
    def fingerprint(key):
        actual = sha((ROOT / key).read_bytes())
        before = next((original[group][key] for group in GROUPS if key in original.get(group, {})), None)
        if actual != before and key in HISTORICAL:
            if key not in preserved or sha(preserved[key]) != before:
                raise ValueError("historical proof input lacks its exact predecessor bytes: " + key)
            historical.setdefault(name, {})[key] = dict(preserved_sha256=before, current_sha256=actual)
            return before
        if actual != before and name == CACHE_RECORD and key in CACHE_INPUTS:
            if sha(caches[key]) != before:
                raise ValueError("historical compiled input lacks its exact predecessor bytes: " + key)
            historical_caches.setdefault(name, {})[key] = dict(preserved_sha256=before, current_sha256=actual)
            return before
        return actual
    return fingerprint


def check_gate():
    before = subprocess.run(["git", "show", BASELINE + ":" + GATE], cwd=ROOT,
                            check=True, capture_output=True).stdout.decode()
    if before.count(GATE_BEFORE) != 1 or (ROOT / GATE).read_text() != before.replace(GATE_BEFORE, GATE_AFTER):
        raise ValueError("foundation gate change exceeds the exact current-helper link adjustment")


def check_operational_consumers():
    import importlib.util
    spec = importlib.util.spec_from_file_location("migration_exact_metadata_adapter", ROOT / OPERATIONAL_CHECKER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.verify_code(module.preimages())


def mask(value, changed):
    result = copy.deepcopy(value)
    for group, bindings in changed.items():
        for key in bindings:
            if key not in result[group]:
                raise ValueError("missing reviewed fingerprint: " + key)
            result[group][key] = "reviewed operational/evidence fingerprint"
    return json.dumps(result, sort_keys=True, separators=(",", ":")).encode()


def amended(original, hashes):
    result, changed = copy.deepcopy(original), {}
    for group in GROUPS:
        for key, before in original.get(group, {}).items():
            after = hashes(key)
            if before != after:
                if key not in ALLOWED:
                    raise ValueError("non-operational proof/source input changed: " + key)
                changed.setdefault(group, {})[key] = dict(before=before, after=after)
                result[group][key] = after
    return result, changed


def apply():
    check_gate()
    check_operational_consumers()
    preserved, predecessor = preserved_inputs()
    caches, compiled_predecessor = preserved_caches()
    entries, historical, historical_caches = {}, {}, {}
    for name in FILES:
        raw, original = original_record(name)
        # Permit the status document, its receipt hashes and the exact metadata adapter.
        # Native/Lean/Rocq proof inputs, declarations and axiom sets cannot be amended.
        fingerprint = current_fingerprints(name, original, preserved, caches, historical, historical_caches)
        updated, changes = amended(original, fingerprint)
        current = decode(name, (ROOT / name).read_bytes())
        # An earlier application may have different approved status-document hashes.
        possible = {group: {key: {} for key in original.get(group, {}) if key in ALLOWED} for group in GROUPS}
        if mask(current, possible) != mask(original, possible):
            raise ValueError("current proof payload differs from the preserved baseline: " + name)
        encoded = encode(name, updated)
        (ROOT / name).write_bytes(encoded)
        entries[name] = dict(original_file_sha256=sha(raw), amended_file_sha256=sha(encoded),
                             unchanged_payload_sha256=sha(mask(original, changes)), changes=changes)
    result = dict(schema="leancage-product-evidence-migration-v1", baseline_commit=BASELINE,
                  reason="Product status and its operational metadata adapter change; existing theorem types, axioms, native/Lean/Rocq proof inputs, checked cache identities and original scope fields are preserved exactly.",
                  migration_checker_sha256=sha(Path(__file__).read_bytes()),
                  operational_checker_sha256=sha((ROOT / OPERATIONAL_CHECKER).read_bytes()),
                  predecessor=predecessor, compiled_predecessor=compiled_predecessor,
                  historical_inputs=historical, historical_caches=historical_caches,
                  entries=entries)
    RECORD.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    check()


def check():
    check_gate()
    check_operational_consumers()
    record = json.loads(RECORD.read_text())
    if record["baseline_commit"] != BASELINE or set(record["entries"]) != set(FILES):
        raise ValueError("product evidence migration baseline/inventory differs")
    if record["migration_checker_sha256"] != sha(Path(__file__).read_bytes()) or record["operational_checker_sha256"] != sha((ROOT / OPERATIONAL_CHECKER).read_bytes()):
        raise ValueError("product evidence migration checker differs")
    preserved, predecessor = preserved_inputs()
    if record.get("predecessor") != predecessor:
        raise ValueError("historical evidence predecessor differs")
    caches, compiled_predecessor = preserved_caches()
    if record.get("compiled_predecessor") != compiled_predecessor:
        raise ValueError("historical compiled predecessor differs")
    historical, historical_caches = {}, {}
    for name, entry in record["entries"].items():
        raw = (ROOT / name).read_bytes()
        current = decode(name, raw)
        original_raw, original = original_record(name)
        expected, changes = amended(original,
            current_fingerprints(name, original, preserved, caches, historical, historical_caches))
        if (entry["original_file_sha256"] != sha(original_raw) or current != expected
                or entry["changes"] != changes or mask(original, changes) != mask(current, changes)):
            raise ValueError("accepted proof payload or exact baseline/current mapping differs: " + name)
        if sha(raw) != entry["amended_file_sha256"] or sha(mask(current, entry["changes"])) != entry["unchanged_payload_sha256"]:
            raise ValueError("amended proof payload/fingerprint differs: " + name)
        for group, bindings in entry["changes"].items():
            if group not in GROUPS or not set(bindings) <= ALLOWED:
                raise ValueError("unapproved evidence migration input")
            for key, binding in bindings.items():
                if current[group][key] != binding["after"] or sha((ROOT / key).read_bytes()) != binding["after"]:
                    raise ValueError("stale operational/evidence input: " + key)
    if record.get("historical_inputs") != historical or record.get("historical_caches") != historical_caches:
        raise ValueError("historical/current input inventory differs")
    print("Product evidence migration checked: original theorem/axiom/source/cache payloads preserved; operational status bindings current.")


def original_file_hash(name):
    check()
    return json.loads(RECORD.read_text())["entries"][name]["original_file_sha256"]


def replay(name, previous):
    """Replay the explicit amendment after an older metadata guard reconstructs its preimage."""
    check()
    entry = json.loads(RECORD.read_text())["entries"][name]
    if sha(mask(previous, entry["changes"])) != entry["unchanged_payload_sha256"]:
        raise ValueError("product amendment changes the original proof payload: " + name)
    result = copy.deepcopy(previous)
    for group, bindings in entry["changes"].items():
        for key, binding in bindings.items():
            if result[group][key] not in (binding["before"], binding["after"]):
                raise ValueError("product amendment preimage differs: " + key)
            result[group][key] = binding["after"]
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--apply", action="store_true", help="explicitly amend only the enumerated operational inputs from the preserved Git baseline")
    args = parser.parse_args()
    try:
        apply() if args.apply else check()
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print("Product evidence migration failed: " + str(error), file=sys.stderr)
        sys.exit(1)
