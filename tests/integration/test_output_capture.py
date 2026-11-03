"""A transient storage error must not corrupt the live collector's bounded prefix."""
# §AR-workspace.transport: Scripted syscalls do not execute the helper's VM-only entry point.
from pathlib import Path
import subprocess
import tempfile
import unittest

PROJECT = Path(__file__).resolve().parents[2]


class OutputCapture(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # §AR-tooling.checks: This test runs before the M3 audit on a fresh CI checkout.
        subprocess.run(['lake', 'build', 'LeanCageM3'], cwd=PROJECT / 'm3',
                       check=True, timeout=180)

    def test_partial_storage_failure_through_publication(self):
        with tempfile.TemporaryDirectory(prefix='capture-') as directory:
            work = Path(directory)
            binary = work / 'capture'
            compiled = subprocess.run(['cc', '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
                                       str(PROJECT / 'tests/reporting/capture.c'), '-o', str(binary)],
                                      check=False, capture_output=True, text=True, timeout=60)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            frame = subprocess.run([str(binary)], check=True, capture_output=True, timeout=10).stdout
            self.assertEqual(len(frame), 160)
            path = work / 'frame'
            path.write_bytes(frame)
            checked = subprocess.run(
                ['lake', 'env', 'lean', '--run', '../tests/reporting/CaptureReport.lean',
                 str(path), str(work)], cwd=PROJECT / 'm3', check=False,
                capture_output=True, text=True, timeout=60)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertIn('capture failure report preserved', checked.stdout)


if __name__ == '__main__':
    unittest.main()
