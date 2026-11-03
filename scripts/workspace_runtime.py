#!/usr/bin/env python3
"""Verify and inspect the pinned M3 runtime without installing or executing it."""
# §AR-workspace.runtime: Compose immutable archive entries in memory; never extract through host
# paths.
import argparse
import gzip
import hashlib
import io
import json
import posixpath
from pathlib import Path
import tarfile
import urllib.request

PROJECT = Path(__file__).resolve().parents[1]
PROFILE = PROJECT / "profiles/m3"
CACHE = PROJECT / ".tools/m3vm/runtime"
MAX_UNCOMPRESSED = 256 * 1024 * 1024


def digest(data):
    return "sha256:" + hashlib.sha256(data).hexdigest()


def canonical_name(name):
    while name.startswith("./"):
        name = name[2:]
    name = name.rstrip("/")
    if not name or name.startswith("/") or any(p in ("", ".", "..") for p in name.split("/")):
        raise ValueError("Unsafe or empty archive member name")
    if "\0" in name:
        raise ValueError("NUL in archive member")
    return name


def load_lock():
    lock = json.loads((PROFILE / "runtime-lock.json").read_text())
    raw = (PROFILE / lock["manifest_file"]).read_bytes()
    if digest(raw) != lock["manifest_digest"]:
        raise ValueError("Runtime manifest identity mismatch")
    manifest = json.loads(raw)
    raw_config = (PROFILE / lock["config_file"]).read_bytes()
    if digest(raw_config) != lock["config_digest"] or manifest["config"]["digest"] != lock["config_digest"]:
        raise ValueError("Runtime config identity mismatch")
    if len(raw_config) != manifest["config"]["size"]:
        raise ValueError("Runtime config size mismatch")
    config = json.loads(raw_config)
    if config["os"] != "linux" or config["architecture"] != "amd64":
        raise ValueError("Unsupported runtime architecture")
    layers = [{k: v for k, v in item.items() if k != "uncompressed_digest"} for item in lock["layers"]]
    if layers != manifest["layers"] or [x["uncompressed_digest"] for x in lock["layers"]] != config["rootfs"]["diff_ids"]:
        raise ValueError("Runtime layer order or identity mismatch")
    return lock


def fetch_layers(lock):
    CACHE.mkdir(parents=True, exist_ok=True)
    missing = [x for x in lock["layers"] if not (CACHE / x["digest"].split(":")[1]).exists()]
    token = None
    if missing:
        url = "https://auth.docker.io/token?service=registry.docker.io&scope=repository:library/python:pull"
        with urllib.request.urlopen(url, timeout=60) as response:
            token = json.load(response)["token"]
    for layer in lock["layers"]:
        path = CACHE / layer["digest"].split(":")[1]
        if not path.exists():
            request = urllib.request.Request(
                f"{lock['registry']}/v2/{lock['repository']}/blobs/{layer['digest']}",
                headers={"Authorization": "Bearer " + token})
            with urllib.request.urlopen(request, timeout=60) as response:
                data = response.read(layer["size"] + 1)
            if len(data) != layer["size"] or digest(data) != layer["digest"]:
                raise ValueError("Downloaded runtime layer mismatch")
            temporary = path.with_suffix(".partial")
            temporary.write_bytes(data)
            temporary.replace(path)
        if path.stat().st_size != layer["size"] or digest(path.read_bytes()) != layer["digest"]:
            raise ValueError("Cached runtime layer mismatch")


def apply_layer(entries, raw):
    """Return an object map, not filesystem writes. Whiteouts affect earlier layers only."""
    result = dict(entries)
    with tarfile.open(fileobj=io.BytesIO(raw), mode="r:") as archive:
        members = []
        seen = set()
        for member in archive:
            if member.name in (".", "./") and member.isdir():
                continue
            name = canonical_name(member.name)
            if name in seen:
                raise ValueError("Duplicate archive member")
            seen.add(name)
            members.append((name, member))
        for name, member in members:
            parent, base = posixpath.split(name)
            if base.startswith(".wh."):
                if not member.isfile() or member.size:
                    raise ValueError("Malformed OCI whiteout")
                if base == ".wh..wh..opq":
                    prefix = parent + "/" if parent else ""
                    result = {k: v for k, v in result.items() if not k.startswith(prefix)}
                else:
                    target = posixpath.join(parent, base[4:])
                    if not base[4:]:
                        raise ValueError("Empty whiteout target")
                    result = {k: v for k, v in result.items() if k != target and not k.startswith(target + "/")}
        for name, member in members:
            if posixpath.basename(name).startswith(".wh."):
                continue
            mode = member.mode & 0o777  # nosuid profile; provenance retains original archive modes
            if member.isdir():
                entry = {"kind": "directory", "mode": mode, "data": b""}
            elif member.isfile():
                if member.size > MAX_UNCOMPRESSED:
                    raise ValueError("Oversized runtime file")
                data = archive.extractfile(member).read(MAX_UNCOMPRESSED + 1)
                if len(data) != member.size:
                    raise ValueError("Incomplete runtime file")
                entry = {"kind": "file", "mode": mode, "data": data}
            elif member.issym():
                if "\0" in member.linkname or not member.linkname:
                    raise ValueError("Malformed symlink")
                entry = {"kind": "symlink", "mode": mode, "data": member.linkname.encode("utf-8")}
            elif member.islnk():
                entry = {"kind": "hardlink", "mode": mode, "data": canonical_name(member.linkname)}
            else:
                raise ValueError("Unsupported special runtime object")
            result[name] = entry
    # Names under symlink ancestors must never be materialized by a host extractor.
    for name in result:
        parent = posixpath.dirname(name)
        while parent:
            if parent in result and result[parent]["kind"] != "directory":
                raise ValueError("Non-directory archive ancestor")
            parent = posixpath.dirname(parent)
    # Hard links refer to the layer's objects now, not a later replacement of their names.
    for name, entry in list(result.items()):
        visited = {name}
        target = entry
        while target["kind"] == "hardlink":
            link = target["data"]
            if link in visited or link not in result:
                raise ValueError("Cyclic or missing hardlink target")
            visited.add(link)
            target = result[link]
        if entry["kind"] == "hardlink":
            if target["kind"] != "file":
                raise ValueError("Hardlink to non-regular object")
            result[name] = dict(target)
    return result


def resolve(entries, name):
    """Resolve image-internal absolute/relative symlinks without touching host files."""
    path = "/" + canonical_name(name.lstrip("/"))
    for _ in range(40):
        parts = path.lstrip("/").split("/")
        for i in range(1, len(parts) + 1):
            prefix = "/".join(parts[:i])
            entry = entries.get(prefix)
            if entry and entry["kind"] == "symlink":
                target = entry["data"].decode("utf-8")
                path = posixpath.normpath(posixpath.join("/", posixpath.dirname(prefix), target, *parts[i:]))
                break
        else:
            return path.lstrip("/")
    raise ValueError("Runtime symlink depth exceeded")


def load_entries(fetch=False):
    lock = load_lock()
    if fetch:
        fetch_layers(lock)
    entries = {}
    for layer in lock["layers"]:
        data = (CACHE / layer["digest"].split(":")[1]).read_bytes()
        if len(data) != layer["size"] or digest(data) != layer["digest"]:
            raise ValueError("Runtime layer identity mismatch")
        with gzip.GzipFile(fileobj=io.BytesIO(data)) as stream:
            raw = stream.read(MAX_UNCOMPRESSED + 1)
        if len(raw) > MAX_UNCOMPRESSED or digest(raw) != layer["uncompressed_digest"]:
            raise ValueError("Runtime uncompressed identity/size mismatch")
        entries = apply_layer(entries, raw)
    for item in lock["entrypoints"].values():
        resolved = resolve(entries, item["path"])
        if "/" + resolved != item["resolved_path"] or digest(entries[resolved]["data"]) != "sha256:" + item["sha256"]:
            raise ValueError("Runtime entrypoint mismatch")
    for item in lock["packages"]:
        resolved = resolve(entries, item["license_notice"])
        if "/" + resolved != item["resolved_license_notice"] or digest(entries[resolved]["data"]) != "sha256:" + item["license_notice_sha256"]:
            raise ValueError("Runtime license notice mismatch")
    return entries


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true")
    args = parser.parse_args()
    files = load_entries(fetch=args.fetch)
    print(f"Verified M3 runtime: {len(files)} filesystem entries; no runtime execution.")
