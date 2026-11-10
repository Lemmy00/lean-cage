#!/usr/bin/env python3
"""Verify the preserved partial host checkpoint without promoting it to acceptance."""
# §AR-host-boundary.acceptance: Checkpoint fingerprints do not establish delivery acceptance.
from pathlib import Path
import gzip
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
RECORD = ROOT / "assurance/host-checkpoint.json"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sources(root=ROOT):
    paths = set()
    for name in ("host", "verification/host", "verification/application"):
        paths.update(p for p in (root / name).rglob("*")
                     if p.is_file() and not {".lake", "__pycache__", "drafts"} & set(p.parts)
                     and (p.suffix in {".lean", ".v", ".py", ".c", ".h", ".json"}
                          or p.name == "lean-toolchain"))
    paths.update(root / name for name in (
        "linux/host_python.c", "linux/host_primitives.c", "linux/host_python_primitives.c",
        "linux/host_python_primitives.h", "python/leancage/native.py", "python/leancage/native_build.py",
        "scripts/audit_host.py", "scripts/host_axiom_query.lean", "M5-CONTINUE.md",
        ".github/workflows/check.yml",
        "docs/functional-spec/FS-host-boundary.md", "docs/architecture/AR-host-boundary.md",
        "docs/decisions/architectural/DA-host-engine.md", "docs/reviews/host-boundary-integration.md"))
    return {str(p.relative_to(root)): digest(p.read_bytes()) for p in sorted(paths)}


def verify_hashes(bindings, root=ROOT):
    for name, expected in bindings.items():
        path = Path(name)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("noncanonical checkpoint path: " + name)
        if digest((root / path).read_bytes()) != expected:
            raise ValueError("checkpoint input differs: " + name)


def verify_comments(root=ROOT):
    amendment = json.loads((root / "assurance/host-source-comment-amendment.json").read_text())
    original = gzip.decompress((root / amendment["before_artifact"]).read_bytes())
    program = gzip.decompress((root / amendment["program_artifact"]).read_bytes())
    if digest(original) != amendment["before_sha256"] or digest(program) != amendment["program_sha256"]:
        raise ValueError("preserved native source/program differs")
    amended = original
    for change in amendment["changes"]:
        before, after = change["before"].encode(), change["after"].encode()
        if not before.lstrip().startswith(b"//") or not after.lstrip().startswith(b"//"):
            raise ValueError("source amendment exceeds line comments")
        if b"\n" in before or b"\n" in after or amended.count(before) != change["occurrences"]:
            raise ValueError("comment amendment has unexpected content/occurrences")
        amended = amended.replace(before, after)
    if amended != (root / "linux/host_python.c").read_bytes() or digest(amended) != amendment["after_sha256"]:
        raise ValueError("current native source exceeds the exact reviewed comment edits")
    if amendment["regenerated_program_sha256"] != digest(program):
        raise ValueError("regenerated program identity differs")


def main():
    record = json.loads(RECORD.read_text())
    if record["schema"] != "leancage-host-partial-checkpoint-v1" or record["accepted_security_delivery"] is not False:
        raise ValueError("unsupported checkpoint or attempted delivery promotion")
    if record["state"] != "paused at explicit user request" or record["delivery"] != "M5.2 incomplete":
        raise ValueError("checkpoint scope differs")
    if record["sources"] != sources():
        raise ValueError("maintained checkpoint source inventory differs")
    verify_hashes(record["archives_and_reviews"])
    verify_comments()
    print("Partial host checkpoint sources and archived evidence match; M5.2 remains incomplete.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        print("Host checkpoint check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
