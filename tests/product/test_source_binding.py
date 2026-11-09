"""Bind VM receipts to the maintained package bytes, even when compatibility paths stay fixed."""
# §AR-workspace.acceptance: Changed executable package bytes invalidate the VM receipt.
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("workspace_source_binding_vm", ROOT / "scripts/run_m3_vm.py")
vm = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vm)


class ExecutableSourceBinding(unittest.TestCase):
    def test_canonical_package_changes_invalidate_the_vm_source_binding(self):
        sources = vm.source_identities()
        required = ("workspace/Main.lean", "workspace/LeanCageM3/Metadata.lean", "workspace/lakefile.lean",
                    "lifecycle/Main.lean", "lifecycle/LeanCageM2/Model.lean", "lifecycle/lakefile.lean",
                    "library/lakefile.lean", "linux/metadata_primitives.c")
        self.assertTrue(set(required) <= sources.keys())
        with tempfile.TemporaryDirectory() as directory:
            isolated = Path(directory)
            # Materialize compatibility and canonical paths independently, so the
            # old alias-only inventory cannot accidentally observe the mutation.
            for name in sources:
                destination = isolated / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes((ROOT / name).read_bytes())
            with mock.patch.object(vm, "PROJECT", isolated):
                before = vm.source_identities()
                for name in ("workspace/LeanCageM3/Metadata.lean", "lifecycle/LeanCageM2/Model.lean"):
                    path = isolated / name
                    path.write_bytes(path.read_bytes() + b"\n-- changed source binding fixture\n")
                    changed = vm.source_identities()
                    self.assertNotEqual(before[name], changed[name])
                    self.assertNotEqual(before, changed)
                self.assertEqual(before["m3/LeanCageM3/Metadata.lean"],
                                 vm.source_identities()["m3/LeanCageM3/Metadata.lean"])


if __name__ == "__main__":
    unittest.main()
