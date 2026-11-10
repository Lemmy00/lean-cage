#!/usr/bin/env python3
"""§FS-host-boundary.snapshot: Independently parse the actual bounded archive/config fixture."""
from pathlib import Path
import struct


def check(directory: Path) -> None:
    raw = (directory / "actual.cpio").read_bytes()
    assert len(raw) <= 4096
    position = 0
    entries = []
    while position < len(raw):
        assert raw[position : position + 6] == b"070701"
        fields = [int(raw[position + 6 + 8 * i : position + 14 + 8 * i], 16) for i in range(13)]
        inode, mode, uid, gid, links, mtime, size, major, minor, rmajor, rminor, namesize, checksum = fields
        assert (uid, gid, links, mtime, major, minor, rmajor, rminor, checksum) == (0, 0, 1, 0, 0, 0, 0, 0, 0)
        start = position + 110
        name = raw[start : start + namesize]
        assert name[-1:] == b"\0" and b"\0" not in name[:-1]
        name = name[:-1].decode("utf-8")
        assert namesize == len(name.encode("utf-8")) + 1
        data_at = (start + namesize + 3) // 4 * 4
        assert raw[start + namesize : data_at] == bytes(data_at - start - namesize)
        data = raw[data_at : data_at + size]
        end = (data_at + size + 3) // 4 * 4
        assert raw[data_at + size : end] == bytes(end - data_at - size)
        entries.append((inode, mode, name, data))
        position = end
    assert entries == [(1, 33024, "dir/é", b"abc"), (2, 0, "TRAILER!!!", b"")]
    assert position == len(raw)
    config = (directory / "actual.config").read_bytes()
    assert len(config) == 152 and config[:8] == b"LCREQ1\0\0"
    assert config[8:40] == b"a" * 32 and config[40:104] == b"b" * 64
    assert struct.unpack("<IQQQQIQ", config[104:]) == (1, 1, 2, 3, 4, 2, 0)


if __name__ == "__main__":
    check(Path(".tools/host/image-proof"))
    print("Independent newc/config parser passed: fields, UTF8, data, NUL, alignment, trailer and ABI.")
