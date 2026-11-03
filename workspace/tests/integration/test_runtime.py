"""Passive archive/lock checks; no workload execution."""
# §AR-workspace.runtime: Reject alias/traversal ambiguity before VM image materialization.
import importlib.util
import io
import json
import shutil
import tempfile
from unittest.mock import patch
from pathlib import Path
import tarfile
import unittest

PROJECT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("m3_runtime", PROJECT / "scripts/m3_runtime.py")
RUNTIME = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNTIME)


def archive(items):
    result = io.BytesIO()
    with tarfile.open(fileobj=result, mode="w") as stream:
        for name, kind, data in items:
            item = tarfile.TarInfo(name)
            item.mode = 0o755 if kind == tarfile.DIRTYPE else 0o644
            item.type = kind
            if kind == tarfile.REGTYPE:
                item.size = len(data)
                stream.addfile(item, io.BytesIO(data))
            else:
                if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE):
                    item.linkname = data.decode()
                stream.addfile(item)
    return result.getvalue()


class Runtime(unittest.TestCase):
    def test_pinned_manifest_config_graph(self):
        lock = RUNTIME.load_lock()
        self.assertEqual(len(lock["packages"]), 97)
        self.assertEqual(len(lock["layers"]), 4)

    def test_changed_runtime_graph_rejected(self):
        for target in ('runtime-manifest.json', 'runtime-config.json', 'layer-order'):
            with tempfile.TemporaryDirectory() as directory:
                profile = Path(directory)
                for name in ('runtime-lock.json', 'runtime-manifest.json', 'runtime-config.json'):
                    shutil.copyfile(RUNTIME.PROFILE / name, profile / name)
                if target == 'layer-order':
                    lock = json.loads((profile / 'runtime-lock.json').read_text())
                    lock['layers'].reverse()
                    (profile / 'runtime-lock.json').write_text(json.dumps(lock))
                else:
                    path = profile / target
                    path.write_bytes(path.read_bytes() + b'\n')
                with self.subTest(target=target), patch.object(RUNTIME, 'PROFILE', profile), self.assertRaises(ValueError):
                    RUNTIME.load_lock()

    def test_traversal_and_absolute_names(self):
        for name in ("/etc/passwd", "../outside", "a/../../outside", "a//b", "a/./b"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                RUNTIME.apply_layer({}, archive([(name, tarfile.REGTYPE, b"bad")]))

    def test_duplicate_members_rejected(self):
        with self.assertRaises(ValueError):
            RUNTIME.apply_layer({}, archive([("a", tarfile.REGTYPE, b"one"), ("a", tarfile.REGTYPE, b"two")]))

    def test_symlink_parent_never_followed(self):
        with self.assertRaises(ValueError):
            RUNTIME.apply_layer({}, archive([("a", tarfile.SYMTYPE, b"/tmp"), ("a/escape", tarfile.REGTYPE, b"bad")]))

    def test_whiteout_applies_only_to_previous_layer(self):
        old = RUNTIME.apply_layer({}, archive([("a", tarfile.REGTYPE, b"old")]))
        new = RUNTIME.apply_layer(old, archive([("a", tarfile.REGTYPE, b"new"), (".wh.a", tarfile.REGTYPE, b"")]))
        self.assertEqual(new["a"]["data"], b"new")
        self.assertEqual(old["a"]["data"], b"old")

    def test_opaque_directory_preserves_new_entries(self):
        old = RUNTIME.apply_layer({}, archive([("d", tarfile.DIRTYPE, b""), ("d/old", tarfile.REGTYPE, b"old")]))
        new = RUNTIME.apply_layer(old, archive([("d/.wh..wh..opq", tarfile.REGTYPE, b""), ("d/new", tarfile.REGTYPE, b"new")]))
        self.assertNotIn("d/old", new)
        self.assertEqual(new["d/new"]["data"], b"new")

    def test_hardlink_holds_previous_bytes_after_replacement(self):
        old = RUNTIME.apply_layer({}, archive([("a", tarfile.REGTYPE, b"old"), ("b", tarfile.LNKTYPE, b"a")]))
        new = RUNTIME.apply_layer(old, archive([("a", tarfile.REGTYPE, b"new")]))
        self.assertEqual(new["b"]["data"], b"old")

    def test_bad_hardlinks_special_files_and_cycles(self):
        for items in ([('a', tarfile.LNKTYPE, b'../outside')], [('a', tarfile.LNKTYPE, b'missing')],
                      [('a', tarfile.LNKTYPE, b'b'), ('b', tarfile.LNKTYPE, b'a')], [('dev', tarfile.CHRTYPE, b'')]):
            with self.subTest(items=items), self.assertRaises(ValueError):
                RUNTIME.apply_layer({}, archive(items))

    def test_image_internal_absolute_symlinks_and_loop_bound(self):
        entries = RUNTIME.apply_layer({}, archive([('usr', tarfile.DIRTYPE, b''), ('usr/a', tarfile.REGTYPE, b'ok'),
                                                  ('bin', tarfile.SYMTYPE, b'/usr')]))
        self.assertEqual(RUNTIME.resolve(entries, '/bin/a'), 'usr/a')
        entries = RUNTIME.apply_layer({}, archive([('a', tarfile.SYMTYPE, b'b'), ('b', tarfile.SYMTYPE, b'a')]))
        with self.assertRaises(ValueError):
            RUNTIME.resolve(entries, 'a')


if __name__ == '__main__':
    unittest.main()
