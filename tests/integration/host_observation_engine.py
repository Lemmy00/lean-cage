#!/usr/bin/python3
"""Bounded protocol fixture for native presentation tests; it starts no VM or workload."""
# §AR-host-boundary.interfaces.gateway: Test projection independently of a production engine claim.
import struct
import sys


class PathBytes(bytes):
    pass


def encode(value):
    if value is None:
        return b"\x00"
    if isinstance(value, bool):
        return b"\x02" if value else b"\x01"
    if isinstance(value, int):
        data = str(value).encode("ascii")
        return b"\x03" + struct.pack("<I", len(data)) + data
    if isinstance(value, str):
        data = value.encode("utf-8")
        return b"\x04" + struct.pack("<Q", len(data)) + data
    if isinstance(value, bytes):
        return (b"\x06" if isinstance(value, PathBytes) else b"\x05") + struct.pack("<Q", len(value)) + value
    if isinstance(value, dict):
        return b"\x08" + struct.pack("<I", len(value)) + b"".join(
            encode(key) + encode(item) for key, item in value.items())
    raise TypeError(type(value))


def main():
    source = sys.stdin.buffer
    header = source.read(112)
    if len(header) != 112 or header[:8] != b"LCHREQ1\x00":
        raise ValueError("invalid projection fixture request")
    command = struct.unpack_from("<I", header, 8)[0]
    sizes = [struct.unpack_from("<Q", header, 20 + 12 * index)[0] for index in range(8)]
    if sum(sizes) > 1024 * 1024:
        raise ValueError("projection fixture request cap")
    fields = [source.read(size) for size in sizes]
    if any(len(field) != size for field, size in zip(fields, sizes)) or source.read(1):
        raise ValueError("truncated or trailing projection fixture bytes")
    if command == 4:
        value = {"bundle_id": "0" * 64, "manifest": {"fixture": "native presentation only"},
                 "manifest_path": PathBytes(fields[0] + b"/manifest.json")}
    elif command == 2:
        output = PathBytes(fields[5]) if fields[5] else None
        value = {"request_id": "projection-fixture", "bundle_id": "0" * 64, "command": "run",
                 "status": "complete", "report": None, "exit_code": 0, "vm_cleanup": "fixture",
                 "error": None, "stdout": b"", "stderr": b"", "files": {}, "output": output,
                 "publication": "fixture", "publication_error": None,
                 "json": {"schema": "native-projection-fixture", "output": output,
                          "request_id": "projection-fixture"}}
    else:
        raise ValueError("unsupported projection fixture command")
    payload = encode(value)
    sys.stdout.buffer.write(b"LCHRES1\x00" + struct.pack("<IIQ", 0, 0, len(payload)) + payload)
    sys.stdout.buffer.flush()


if __name__ == "__main__":
    main()
