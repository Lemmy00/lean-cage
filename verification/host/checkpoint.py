#!/usr/bin/env python3
"""Verify the preserved partial host checkpoint without promoting it to acceptance."""
# §AR-host-boundary.acceptance: Checkpoint fingerprints do not establish delivery acceptance.
from pathlib import Path
import gzip
import hashlib
import json
import re
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
    paths.update((root / "tests/integration").glob("host_*.py"))
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
    if digest(amended) != amendment["after_sha256"]:
        raise ValueError("native comment amendment differs")
    if amendment["regenerated_program_sha256"] != digest(program):
        raise ValueError("regenerated program identity differs")
    return amended, program


def unchanged_functions(before, after, selected):
    """Compare exact C bytes outside the separately reviewed function bodies."""
    def erase(source):
        for name in selected:
            pattern = rb"^static PyObject \*" + re.escape(name.encode()) + rb"\([^\n]*\) \{\n.*?^}\n"
            source, count = re.subn(pattern, ("REVIEWED_FUNCTION_" + name + "\n").encode(),
                                    source, flags=re.M | re.S)
            if count != 1:
                raise ValueError("reviewed function boundary differs: " + name)
        return source
    if erase(before) != erase(after):
        raise ValueError("native amendment changes an unreviewed function or other source bytes")


def verify_native_epochs(chain, root=ROOT):
    """Retain historical claims while composing explicit behavioral amendments."""
    current, program = verify_comments(root)
    expected_names = [("observation", ["host_outcome_observation"]),
                      ("outcome", ["host_outcome_from", "host_outcome_json"])]
    if len(chain) != len(expected_names):
        raise ValueError("native source epoch chain differs")
    for epoch, (name, functions) in zip(chain, expected_names):
        if epoch["name"] != name or epoch["functions"] != functions:
            raise ValueError("native epoch review scope differs")
        amendment = json.loads((root / epoch["amendment"]).read_text())
        if amendment["accepted_security_delivery"] is not False:
            raise ValueError("source amendment attempts delivery promotion")
        if digest(current) != amendment["before_c_sha256"] or digest(program) != amendment["before_clight_sha256"]:
            raise ValueError("native epoch predecessor differs: " + name)
        after = gzip.decompress((root / epoch["after_source"]).read_bytes())
        translated = gzip.decompress((root / epoch["after_program"]).read_bytes())
        if digest(after) != amendment["after_c_sha256"] or digest(translated) != amendment["after_clight_sha256"]:
            raise ValueError("native epoch successor differs: " + name)
        unchanged_functions(current, after, functions)
        verify_hashes(amendment["artifacts"], root)
        proof = amendment["source_retention_proof"]
        verify_hashes({proof["path"]: proof["sha256"]}, root)
        current, program = after, translated
    if current != (root / "linux/host_python.c").read_bytes():
        raise ValueError("current native source exceeds the reviewed epoch chain")
    return program


def verify_archived_replay(binding, program, root=ROOT):
    inputs_bytes = gzip.decompress((root / binding["inputs"]).read_bytes())
    replay = json.loads(gzip.decompress((root / binding["result"]).read_bytes()))
    inputs = json.loads(inputs_bytes)
    if (replay["status"] != "passed" or replay["excluded"] or replay["failed"]
            or replay["blocked"] or replay["input_drift"] or replay.get("partial") is not False
            or digest(inputs_bytes) != replay["inputs_sha256"]
            or replay.get("aggregate_error") is not None or not replay["aggregate_object_sha256"]):
        raise ValueError("complete source replay evidence differs")
    maintained = {path.stem: path for path in (root / "verification/host").glob("*.v")}
    if sorted(maintained) != inputs["maintained_sources"]:
        raise ValueError("source replay maintained inventory differs")
    for name, path in maintained.items():
        expected = digest(path.read_bytes())
        if (inputs["sources"][name] != str(path.relative_to(root))
                or inputs["source_sha256"][name] != expected
                or replay["completed"][name]["source"] != expected):
            raise ValueError("source replay input differs: " + name)
    if (inputs["source_sha256"]["GatewaySource"] != digest(program)
            or replay["completed"]["GatewaySource"]["source"] != digest(program)):
        raise ValueError("source replay generated native program differs")
    verify_hashes({"m4/bridge/profile.py": inputs["profile_sha256"],
                   "m4/bridge/toolchain-lock.json": inputs["lock_sha256"],
                   "verification/host/source_replay.py": inputs["replay_tool_sha256"]}, root)
    kernel = gzip.decompress((root / binding["kernel"]).read_bytes())
    if digest(kernel) != replay["checker_stdout_sha256"]:
        raise ValueError("source replay independent-check diagnostics differ")


def verify_source_eof(root=ROOT):
    amendment = json.loads((root / "assurance/host-source-eof-amendment.json").read_text())
    expected = {"verification/host/" + name for name in (
        "GatewayBuiltinTypeSource.v", "GatewayOutcomeEntry.v", "GatewayOutcomeGetterSource.v",
        "GatewayOutcomeValidationPaths.v", "GatewaySourceFraming.v", "PositionalCopyNative.lean")}
    if (amendment["schema"] != "leancage-host-source-eof-amendment-v1"
            or amendment["accepted_security_delivery"] is not False or set(amendment["sources"]) != expected):
        raise ValueError("source EOF amendment scope differs")
    for name, row in amendment["sources"].items():
        before = gzip.decompress((root / row["before_artifact"]).read_bytes())
        after = (root / name).read_bytes()
        if (digest(before) != row["before_sha256"] or digest(after) != row["after_sha256"]
                or before == after or before.rstrip(b"\n") + b"\n" != after):
            raise ValueError("source EOF amendment exceeds terminal LF bytes: " + name)
    return amendment["sources"]


def verify_copy_offsets(path, root=ROOT):
    amendment = json.loads((root / path).read_text())
    if (amendment["schema"] != "leancage-host-file-copy-offset-amendment-v1"
            or amendment["accepted_security_delivery"] is not False):
        raise ValueError("unsupported file-copy amendment or attempted promotion")
    before = gzip.decompress((root / amendment["before_c_artifact"]).read_bytes())
    after = gzip.decompress((root / amendment["after_c_artifact"]).read_bytes())
    if digest(before) != amendment["before_c_sha256"] or digest(after) != amendment["after_c_sha256"]:
        raise ValueError("file-copy adapter source epoch differs")
    pattern = rb"^    case 1:\n.*?(?=^    case 2:)"
    def erase(source):
        retained, count = re.subn(pattern, b"REVIEWED_READ_CASE\n", source, flags=re.M | re.S)
        if count != 1:
            raise ValueError("file-read primitive boundary differs")
        return retained
    if erase(before) != erase(after) or after != (root / "linux/host_primitives.c").read_bytes():
        raise ValueError("file-copy repair exceeds the reviewed single-op delta")
    verify_hashes(amendment["artifacts"], root)
    eof = verify_source_eof(root)
    for name, expected in amendment["source_sha256"].items():
        current = digest((root / name).read_bytes())
        if current != expected and not (name in eof and eof[name]["before_sha256"] == expected
                                        and eof[name]["after_sha256"] == current):
            raise ValueError("file-copy source binding differs: " + name)
    predecessor = amendment["predecessor"]
    verify_hashes({predecessor["path"]: predecessor["sha256"]}, root)
    return before


def verify_record(record, root=ROOT):
    if record["schema"] != "leancage-host-partial-checkpoint-v2" or record["accepted_security_delivery"] is not False:
        raise ValueError("unsupported checkpoint or attempted delivery promotion")
    if record["state"] != "active implementation" or record["delivery"] != "M5.2 incomplete":
        raise ValueError("checkpoint scope differs")
    predecessor = record["predecessor"]
    packed = (root / predecessor["path"]).read_bytes()
    if digest(packed) != predecessor["sha256"]:
        raise ValueError("historical checkpoint archive differs")
    historical = json.loads(gzip.decompress(packed))
    if (historical["schema"] != "leancage-host-partial-checkpoint-v1"
            or historical["state"] != "paused at explicit user request"
            or historical["accepted_security_delivery"] is not False):
        raise ValueError("historical checkpoint scope differs")
    updates = record["reviewed_metadata_updates"]
    expected_updates = {"assurance/host-ownership-status.json", "assurance/host-response-obligations.json",
                        "verification/host/drafts/framing/README.md"}
    if set(updates) != expected_updates:
        raise ValueError("checkpoint metadata amendment scope differs")
    for name, amendment in updates.items():
        if amendment["before_artifact"] not in record["archives_and_reviews"]:
            raise ValueError("metadata predecessor archive is unbound: " + name)
        before = gzip.decompress((root / amendment["before_artifact"]).read_bytes())
        if (digest(before) != historical["archives_and_reviews"][name]
                or digest(before) != amendment["before_sha256"]
                or digest((root / name).read_bytes()) != amendment["after_sha256"]
                or record["archives_and_reviews"].get(name) != amendment["after_sha256"]
                or not amendment["review"]):
            raise ValueError("reviewed metadata amendment differs: " + name)
        if name.endswith(".json"):
            current = json.loads((root / name).read_text())
            if current["accepted_security_delivery"] is not False:
                raise ValueError("metadata amendment attempts delivery promotion: " + name)
    if record["sources"] != sources(root):
        raise ValueError("maintained checkpoint source inventory differs")
    verify_hashes(record["archives_and_reviews"], root)
    program = verify_native_epochs(record["native_epochs"], root)
    verify_archived_replay(record["rocq_source_replay"], program, root)
    close = record["directory_close_inputs"]
    if set(close) != {"host/LeanCageHost/Snapshot.lean", "linux/host_primitives.c",
                      "verification/host/DirectoryCloseNative.lean"}:
        raise ValueError("directory-close ABI input scope differs")
    before_read_repair = verify_copy_offsets(record["file_copy_offset_amendment"], root)
    verify_hashes({name: sha for name, sha in close.items() if name != "linux/host_primitives.c"}, root)
    if digest(before_read_repair) != close["linux/host_primitives.c"]:
        raise ValueError("file-copy repair predecessor is not the reviewed directory-close adapter")
    reviewed_close = json.loads((root / "assurance/host-inherited-channel-review.json").read_text())
    if any(reviewed_close["sourceSha256"].get(name) != sha for name, sha in close.items()):
        raise ValueError("directory-close inputs exceed the reviewed ABI change")


def main():
    record = json.loads(RECORD.read_text())
    verify_record(record)
    print("Partial host checkpoint sources and archived evidence match; M5.2 remains incomplete.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        print("Host checkpoint check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
