"""Strict streaming decoder for the VM's dedicated result channel."""
# §AR-workspace-vm.channel: Only fixed tags and bound bytes cross the control boundary.
import json
import struct
from .snapshots import digest, MANIFEST_MAX

MAGIC = b"LCVM1\0\0\0"
HEADER = struct.Struct("<IIQ")
TERMINAL = struct.Struct("<IIII")
REPORT, STORED, STDOUT, STDERR, EXPORT, BLOB, END = range(1, 8)


def strict_json(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate result JSON key")
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=unique)


class Decoder:
    def __init__(self, request_id, bundle_id, limits):
        self.prefix = MAGIC + request_id.encode("ascii") + bundle_id.encode("ascii")
        self.limits = limits
        self.buffer = bytearray()
        self.started = False
        self.header = None
        self.records = {}
        self.blobs = {}
        self.total_blobs = 0
        self.terminal = None

    @property
    def report(self):
        data = self.records.get(REPORT)
        if data is None:
            return None
        try:
            result = strict_json(data)
        except (ValueError, UnicodeError):
            return None
        return result if isinstance(result, dict) else None

    def feed(self, data):
        # The caller reads at most 64 KiB at a time; do not buffer unbounded headers.
        if self.terminal is not None and data:
            raise ValueError("trailing result bytes")
        self.buffer.extend(data)
        if not self.started:
            size = min(len(self.buffer), len(self.prefix))
            if self.buffer[:size] != self.prefix[:size]:
                raise ValueError("VM result request/bundle identity differs")
            if len(self.buffer) < len(self.prefix):
                return
            del self.buffer[:len(self.prefix)]
            self.started = True
        while True:
            if self.header is None:
                if len(self.buffer) < HEADER.size:
                    return
                tag, reserved, size = HEADER.unpack(self.buffer[:HEADER.size])
                del self.buffer[:HEADER.size]
                caps = {REPORT: 65536, STORED: 65536, STDOUT: self.limits["stdout_max_bytes"],
                        STDERR: self.limits["stderr_max_bytes"], EXPORT: MANIFEST_MAX,
                        BLOB: 64 + self.limits["workspace_max_bytes"], END: TERMINAL.size}
                if reserved or tag not in caps or size > caps[tag] or (tag != BLOB and tag in self.records):
                    raise ValueError("invalid/duplicate/oversized result record")
                if tag == BLOB and (size < 64 or len(self.blobs) >= self.limits["workspace_max_inodes"]
                                    or self.total_blobs + size - 64 > self.limits["workspace_max_bytes"]):
                    raise ValueError("export aggregate bound exceeded")
                self.header = tag, size
            tag, size = self.header
            if len(self.buffer) < size:
                return
            payload = bytes(self.buffer[:size])
            del self.buffer[:size]
            self.header = None
            if tag == BLOB:
                sha = payload[:64].decode("ascii")
                content = payload[64:]
                if sha in self.blobs or digest(content) != sha:
                    raise ValueError("duplicate or corrupt export blob")
                self.total_blobs += len(content)
                self.blobs[sha] = content
            else:
                self.records[tag] = payload
            if tag == END:
                if size != TERMINAL.size or self.buffer:
                    raise ValueError("invalid terminal result")
                self.terminal = TERMINAL.unpack(payload)
                return

    def finish(self):
        if not self.started or self.terminal is None or self.header is not None or self.buffer:
            raise ValueError("incomplete VM result channel")
        if REPORT not in self.records:
            raise ValueError("missing controller result")
        controller, retrieved, error, extinct = self.terminal
        if controller > 255 or retrieved > 255 or error > 4095 or extinct > 1:
            raise ValueError("terminal status is outside the supported bounds")
        return self.terminal
