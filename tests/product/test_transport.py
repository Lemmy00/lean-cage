"""Adversarial request/result boundary tests; no guest execution on the host."""
# §AR-workspace-vm.request: Reject aliasing, mutation and bound violations before boot.
# §AR-workspace-vm.channel: Spoofed, partial and unsafe returned artifacts fail closed.
import copy
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "python"))
from leancage.protocol import Decoder, MAGIC, HEADER, TERMINAL, REPORT, STDOUT, BLOB, END
from leancage.runner import Workspace, Outcome, rename_new
from leancage.snapshots import digest, snapshot, parse_export, write_exports

LIMITS = json.loads((ROOT / "profiles/offline-workspace/example-policy.json").read_text())["limits"]


class Snapshots(unittest.TestCase):
    def test_frozen_input_and_stdin_are_content_addressed(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "sub").mkdir()
            (root / "sub/input").write_bytes(b"caller input\n")
            frozen = snapshot(root, b"stdin\n", LIMITS)
            (root / "sub/input").write_bytes(b"later edit")
            self.assertEqual(frozen.blobs[digest(b"caller input\n")], b"caller input\n")
            self.assertEqual(frozen.stdin_identity, "sha256:" + digest(b"stdin\n"))
            self.assertIn(b"D 737562\n", frozen.tree)

    def test_symlink_hardlink_fifo_and_reserved_names_rejected(self):
        for kind in ("symlink", "hardlink", "fifo", "reserved"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as d:
                root = Path(d)
                (root / "source").write_bytes(b"x")
                if kind == "symlink":
                    (root / "link").symlink_to("source")
                elif kind == "hardlink":
                    os.link(root / "source", root / "link")
                elif kind == "fifo":
                    os.mkfifo(root / "fifo")
                else:
                    (root / ".tmp").mkdir()
                with self.assertRaises(ValueError):
                    snapshot(root, None, LIMITS)

    def test_byte_inode_stdin_and_depth_bounds(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "large").write_bytes(b"four")
            for changed in ({"workspace_max_bytes": 3}, {"workspace_max_inodes": 2}):
                with self.subTest(changed=changed), self.assertRaises(ValueError):
                    snapshot(root, None, dict(LIMITS, **changed))
            with self.assertRaises(ValueError):
                snapshot(None, b"four", dict(LIMITS, stdin_max_bytes=3))
            (root / "large").unlink()
            parent = root
            for _ in range(65):
                parent = parent / "d"
                parent.mkdir()
            with self.assertRaises(ValueError):
                snapshot(root, None, LIMITS)

    def test_export_safe_files_and_empty_directories(self):
        payload = b"returned file\0\xff"
        manifest = b"LCEXPORT1\nD 737562\nF 0 7375622f726573756c74 " + str(len(payload)).encode() + b" " + digest(payload).encode() + b"\nD 2e746d70\n"
        entries, directories = parse_export(manifest, digest(manifest), {digest(payload): payload}, LIMITS)
        with tempfile.TemporaryDirectory() as d:
            write_exports(Path(d), entries, directories)
            self.assertEqual((Path(d) / "sub/result").read_bytes(), payload)
            self.assertTrue((Path(d) / ".tmp").is_dir())

    def test_export_traversal_alias_conflict_size_and_hash_rejected(self):
        sha = digest(b"x").encode()
        for body in (b"F 0 2e2e2f657363617065 1 " + sha + b"\n",
                     b"F 0 2f657363617065 1 " + sha + b"\n",
                     b"D 61\nD 61\n",
                     b"F 0 61 1 " + sha + b"\nF 0 612f62 1 " + sha + b"\n",
                     b"F 0 61 2 " + sha + b"\n",
                     b"F 0 ff 1 " + sha + b"\n"):
            manifest = b"LCEXPORT1\n" + body
            with self.subTest(body=body), self.assertRaises(ValueError):
                parse_export(manifest, digest(manifest), {sha.decode(): b"x"}, LIMITS)
        with self.assertRaises(ValueError):
            parse_export(b"LCEXPORT1\n", "0"*64, {}, LIMITS)


class Framing(unittest.TestCase):
    request, bundle = "a"*32, "b"*64

    def prefix(self):
        return MAGIC + self.request.encode() + self.bundle.encode()

    def decoder(self):
        return Decoder(self.request, self.bundle, dict(LIMITS, stdout_max_bytes=8, workspace_max_bytes=32, workspace_max_inodes=2))

    @staticmethod
    def record(tag, payload):
        return HEADER.pack(tag, 0, len(payload)) + payload

    def test_every_stream_split_and_guest_magic_are_unambiguous(self):
        wire = self.prefix() + self.record(REPORT, b'{"schema":"test"}') + self.record(STDOUT, MAGIC) + self.record(END, TERMINAL.pack(0, 0, 0, 1))
        for split in range(len(wire)+1):
            decoder = self.decoder()
            decoder.feed(wire[:split]); decoder.feed(wire[split:]); decoder.finish()
            self.assertEqual(decoder.records[STDOUT], MAGIC)

    def test_all_truncated_prefixes_fail(self):
        wire = self.prefix() + self.record(REPORT, b"{}") + self.record(END, TERMINAL.pack(0, 0, 0, 1))
        for size in range(len(wire)):
            decoder = self.decoder()
            decoder.feed(wire[:size])
            with self.assertRaises(ValueError):
                decoder.finish()

    def test_wrong_request_bundle_unknown_tag_reserved_and_oversize_fail(self):
        samples = [b"x" + self.prefix()[1:], MAGIC + b"c"*32 + self.bundle.encode(),
                   self.prefix() + HEADER.pack(8, 0, 0), self.prefix() + HEADER.pack(REPORT, 1, 0),
                   self.prefix() + HEADER.pack(STDOUT, 0, 9),
                   self.prefix() + HEADER.pack(BLOB, 0, 97)]
        for wire in samples:
            with self.subTest(wire=wire), self.assertRaises(ValueError):
                self.decoder().feed(wire)

    def test_duplicate_reports_blobs_and_trailing_bytes_fail(self):
        blob = digest(b"x").encode() + b"x"
        for records in (self.record(REPORT, b"{}")*2, self.record(BLOB, blob)*2,
                        self.record(END, TERMINAL.pack(0, 0, 0, 1)) + b"x"):
            with self.subTest(), self.assertRaises(ValueError):
                self.decoder().feed(self.prefix() + records)

    def test_terminal_status_bounds_are_checked(self):
        for values in ((256, 0, 0, 1), (0, 256, 0, 1), (0, 0, 4096, 1), (0, 0, 0, 2)):
            decoder = self.decoder()
            decoder.feed(self.prefix() + self.record(REPORT, b"{}") + self.record(END, TERMINAL.pack(*values)))
            with self.assertRaises(ValueError):
                decoder.finish()

    def test_late_channel_loss_preserves_known_report(self):
        report = dict(schema="leancage-result-v1", run_id=1, entry="yes", cleanup="complete")
        decoder = self.decoder()
        decoder.feed(self.prefix() + self.record(REPORT, json.dumps(report).encode()))
        with self.assertRaises(ValueError):
            decoder.finish()
        self.assertEqual(Workspace._known_report(decoder.report, "run"), report)

    def test_preflight_failure_keeps_its_allocated_identity(self):
        report = dict(schema="leancage-result-v1", run_id=1, entry="no", cleanup="complete", termination="setup_failed")
        self.assertEqual(Workspace._known_report(report, "check"), report)
        self.assertIsNone(Workspace._known_report(dict(report, run_id=2), "check"))
        self.assertIsNone(Workspace._known_report(dict(report, entry="yes"), "check"))


class Publication(unittest.TestCase):
    def test_atomic_publish_never_replaces_a_target(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "source").mkdir(); (root / "target").mkdir()
            (root / "target/keep").write_text("previous run")
            with self.assertRaises(FileExistsError):
                rename_new(root / "source", root / "target")
            self.assertEqual((root / "target/keep").read_text(), "previous run")

    def test_storage_failure_keeps_observed_report(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "parent").write_text("cannot contain a result directory")
            api = object.__new__(Workspace)
            api.results = root
            decoder = Decoder("a"*32, "b"*64, LIMITS)
            report = dict(entry="yes", termination="exited", cleanup="complete")
            result = Outcome("a"*32, "b"*64, "run", "complete", report, 0, "complete")
            api._publish(result, b"{}", b"", decoder, [], [], root / "parent/result")
            self.assertEqual(result.report, report)
            self.assertEqual(result.publication, "failed")
            self.assertEqual(result.exit_code, 126)


if __name__ == "__main__":
    unittest.main()
