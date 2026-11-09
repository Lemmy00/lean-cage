"""Read the preserved workspace evidence without treating it as current execution."""
# §AR-workspace-vm.migration: A current revision preserves complete predecessor inputs and claims.
import base64
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT / "assurance/workspace-baseline.json.gz"
REVISION = "be541b134bd339fb053f07c491e04ec995d564f8"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_baseline():
    record = json.loads(gzip.decompress(ARCHIVE.read_bytes()))
    if set(record) != {"schema", "revision", "files"} or record["schema"] != "leancage-workspace-baseline-v1" or record["revision"] != REVISION:
        raise ValueError("workspace predecessor archive schema/revision differs")
    files = {}
    for name, entry in record["files"].items():
        if name.startswith("/") or any(part in ("", ".", "..") for part in name.split("/")) or set(entry) != {"sha256", "base64"}:
            raise ValueError("noncanonical workspace predecessor path/entry")
        data = base64.b64decode(entry["base64"], validate=True)
        if sha(data) != entry["sha256"]:
            raise ValueError("workspace predecessor bytes differ: " + name)
        files[name] = data
    claims = json.loads(files["assurance/m3-claims.json"])
    evidence = json.loads(files["assurance/m3-vm-evidence.json"])
    for name, digest in claims["source_sha256"].items():
        if name not in files or sha(files[name]) != digest:
            raise ValueError("workspace predecessor claim input differs: " + name)
    for name, digest in evidence["source_sha256"].items():
        if name not in files or sha(files[name]) != digest:
            raise ValueError("workspace predecessor VM input differs: " + name)
    reporting = json.loads(gzip.decompress(files["assurance/reporting-source.json.gz"]))
    for name, digest in reporting["inputs_sha256"].items():
        if name not in files or sha(files[name]) != digest:
            raise ValueError("workspace predecessor source proof input differs: " + name)
    for name, key in (("assurance/m3-vm-transcript.log", "transcript_sha256"),
                      ("assurance/m3-image-inventory.json", "inventory_sha256")):
        if sha(files[name]) != evidence[key]:
            raise ValueError("workspace predecessor VM receipt differs: " + name)
    return files


def binding():
    files = read_baseline()
    return dict(archive=str(ARCHIVE.relative_to(ROOT)), archive_sha256=sha(ARCHIVE.read_bytes()), revision=REVISION,
                records_sha256={name: sha(files[name]) for name in (
                    "assurance/m3-claims.json", "assurance/m3-vm-evidence.json",
                    "assurance/m3-image-inventory.json", "assurance/m3-vm-transcript.log",
                    "assurance/reporting-source.json.gz")})
