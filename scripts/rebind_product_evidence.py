#!/usr/bin/env python3
"""Amend operational status fingerprints while freezing every original proof field."""
# §AR-workspace-vm.migration: Preserve original types, axioms, source proofs and cache identities.
import argparse
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
FILES = ["assurance/filter-decoder.json", "assurance/m2-claims.json", "assurance/m3-claims.json",
         "assurance/reporting-source.json.gz", "assurance/reporting-connection.json.gz",
         "assurance/reporting-compiler.json.gz"]
OPERATIONAL_CHECKER = "verification/compiler/amendment.py"
ALLOWED = {"docs/functional-spec/FS-assurance.md", OPERATIONAL_CHECKER, *FILES}
GROUPS = ("source_sha256", "inputs_sha256")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def decode(name, raw):
    return json.loads(gzip.decompress(raw) if name.endswith(".gz") else raw)


def encode(name, value):
    data = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    return gzip.compress(data, mtime=0) if name.endswith(".gz") else data


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
    entries = {}
    for name in FILES:
        raw = subprocess.run(["git", "show", BASELINE + ":" + name], cwd=ROOT, check=True, capture_output=True).stdout
        original = decode(name, raw)
        # Permit the status document, its receipt hashes and the exact metadata adapter.
        # Native/Lean/Rocq proof inputs, declarations and axiom sets cannot be amended.
        updated, changes = amended(original, lambda key: sha((ROOT / key).read_bytes()))
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
                  entries=entries)
    RECORD.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    check()


def check():
    record = json.loads(RECORD.read_text())
    if record["baseline_commit"] != BASELINE or set(record["entries"]) != set(FILES):
        raise ValueError("product evidence migration baseline/inventory differs")
    if record["migration_checker_sha256"] != sha(Path(__file__).read_bytes()) or record["operational_checker_sha256"] != sha((ROOT / OPERATIONAL_CHECKER).read_bytes()):
        raise ValueError("product evidence migration checker differs")
    for name, entry in record["entries"].items():
        raw = (ROOT / name).read_bytes()
        current = decode(name, raw)
        if sha(raw) != entry["amended_file_sha256"] or sha(mask(current, entry["changes"])) != entry["unchanged_payload_sha256"]:
            raise ValueError("amended proof payload/fingerprint differs: " + name)
        for group, bindings in entry["changes"].items():
            if group not in GROUPS or not set(bindings) <= ALLOWED:
                raise ValueError("unapproved evidence migration input")
            for key, binding in bindings.items():
                if current[group][key] != binding["after"] or sha((ROOT / key).read_bytes()) != binding["after"]:
                    raise ValueError("stale operational/evidence input: " + key)
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
