"""Bounded snapshots and the existing content-addressed tree/export formats."""
# §AR-workspace-vm.request: Snapshot through owned descriptors; never follow caller links.
from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
import stat

TREE_MAX = 4 * 1024 * 1024
MANIFEST_MAX = 16 * 1024 * 1024


def digest(data):
    return hashlib.sha256(data).hexdigest()


def path_bytes(name, reserved=True):
    raw = name.encode("utf-8", errors="strict")
    parts = raw.split(b"/")
    if (not raw or len(raw) > 4095 or len(parts) > 64 or b"\0" in raw
            or any(p in (b"", b".", b"..") or len(p) > 255 for p in parts)
            or (reserved and parts[0] == b".tmp")):
        raise ValueError("unsupported snapshot/export path")
    return raw


def read_regular(path, limit):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    try:
        return read_fd(fd, limit)
    finally:
        os.close(fd)


def read_fd(fd, limit):
    before = os.fstat(fd)
    if not stat.S_ISREG(before.st_mode) or before.st_size > limit:
        raise ValueError("input is not a bounded regular file")
    data = bytearray()
    while len(data) <= limit:
        chunk = os.read(fd, min(65536, limit + 1 - len(data)))
        if not chunk:
            break
        data.extend(chunk)
    after = os.fstat(fd)
    if len(data) > limit or len(data) != before.st_size or (
            before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (
            after.st_size, after.st_mtime_ns, after.st_ctime_ns):
        raise ValueError("input changed during bounded snapshot")
    return bytes(data)


@dataclass(frozen=True)
class Snapshot:
    tree: bytes | None
    stdin: bytes | None
    blobs: dict

    @property
    def workspace_identity(self):
        return "sha256:" + digest(self.tree) if self.tree is not None else None

    @property
    def stdin_identity(self):
        return "sha256:" + digest(self.stdin) if self.stdin is not None else None


def snapshot(workspace, stdin, limits):
    blobs, lines = {}, [b"LCTREE1\n"]
    count, total, tree_size = 2, 0, 8

    def append(line):
        nonlocal tree_size
        tree_size += len(line)
        if tree_size > TREE_MAX:
            raise ValueError("input tree exceeds 4 MiB")
        lines.append(line)

    def walk(fd, prefix):
        nonlocal count, total
        before = os.fstat(fd)
        for base in sorted(os.listdir(fd), key=lambda s: s.encode("utf-8", "strict")):
            name = prefix + base
            encoded = path_bytes(name).hex().encode("ascii")
            count += 1
            if count > limits["workspace_max_inodes"]:
                raise ValueError("input exceeds workspace inode limit")
            info = os.stat(base, dir_fd=fd, follow_symlinks=False)
            if stat.S_ISDIR(info.st_mode):
                child = os.open(base, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=fd)
                try:
                    if os.fstat(child).st_ino != info.st_ino:
                        raise ValueError("directory changed during snapshot")
                    append(b"D " + encoded + b"\n")
                    walk(child, name + "/")
                finally:
                    os.close(child)
            elif stat.S_ISREG(info.st_mode) and info.st_nlink == 1:
                child = os.open(base, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC, dir_fd=fd)
                try:
                    actual = os.fstat(child)
                    if (actual.st_dev, actual.st_ino, actual.st_nlink) != (info.st_dev, info.st_ino, 1):
                        raise ValueError("file changed during snapshot")
                    data = read_fd(child, limits["workspace_max_bytes"] - total)
                finally:
                    os.close(child)
                total += len(data)
                sha = digest(data)
                blobs[sha] = data
                executable = b"1" if info.st_mode & 0o111 else b"0"
                append(b"F " + executable + b" " + encoded + b" " + str(len(data)).encode() + b" " + sha.encode() + b"\n")
            else:
                raise ValueError("input links and special files are unsupported")
        after = os.fstat(fd)
        if (before.st_mtime_ns, before.st_ctime_ns) != (after.st_mtime_ns, after.st_ctime_ns):
            raise ValueError("directory changed during snapshot")

    if workspace is not None:
        fd = os.open(workspace, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC)
        try:
            walk(fd, "")
        finally:
            os.close(fd)
    input_bytes = None if stdin is None else (
        stdin if isinstance(stdin, bytes) else read_regular(stdin, limits["stdin_max_bytes"]))
    if input_bytes is not None:
        if len(input_bytes) > limits["stdin_max_bytes"]:
            raise ValueError("stdin exceeds policy limit")
        blobs[digest(input_bytes)] = input_bytes
    return Snapshot(b"".join(lines) if workspace is not None else None, input_bytes, blobs)


# §AR-workspace-vm.channel: Guest names have no authority until the complete export is validated.
def parse_export(data, expected_digest, blobs, limits):
    if len(data) > MANIFEST_MAX or digest(data) != expected_digest or not data.startswith(b"LCEXPORT1\n") or not data.endswith(b"\n"):
        raise ValueError("invalid export manifest identity/format")
    entries, names, required = [], {}, set()
    total = 0
    for line in data.split(b"\n")[1:-1]:
        fields = line.split(b" ")
        tag = fields[0]
        if tag in (b"D", b"O") and len(fields) == 2:
            encoded = fields[1]
        elif tag == b"F" and len(fields) == 5 and fields[1] in (b"0", b"1"):
            encoded = fields[2]
        else:
            raise ValueError("invalid export entry")
        try:
            name = bytes.fromhex(encoded.decode("ascii")).decode("utf-8", "strict")
        except (ValueError, UnicodeError) as error:
            raise ValueError("invalid export path encoding") from error
        if path_bytes(name, reserved=False).hex().encode() != encoded or name in names:
            raise ValueError("duplicate/noncanonical export path")
        names[name] = tag
        if len(names) > limits["workspace_max_inodes"]:
            raise ValueError("export inode limit exceeded")
        if tag == b"F":
            if not fields[3].isdigit() or str(int(fields[3])).encode() != fields[3]:
                raise ValueError("invalid export byte count")
            size = int(fields[3])
            sha = fields[4].decode("ascii")
            payload = blobs.get(sha)
            total += size
            if payload is None or len(payload) != size or digest(payload) != sha or total > limits["workspace_max_bytes"]:
                raise ValueError("export blob identity/size differs")
            required.add(sha)
            entries.append((name, payload, fields[1] == b"1"))
    for name in names:
        for parent in Path(name).parents:
            if str(parent) != "." and names.get(str(parent)) != b"D":
                raise ValueError("missing or conflicting export directory")
    if set(blobs) != required:
        raise ValueError("unreferenced export blob")
    return entries, [name for name, kind in names.items() if kind == b"D"]


def write_exports(root, entries, directories):
    for name in sorted(directories, key=lambda n: (n.count("/"), n)):
        (root / name).mkdir(mode=0o700)
    for name, data, executable in entries:
        fd = os.open(root / name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o700 if executable else 0o600)
        with os.fdopen(fd, "wb") as output:
            output.write(data)
