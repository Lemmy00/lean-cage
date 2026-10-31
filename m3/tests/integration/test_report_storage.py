"""Report publication preserves known outcomes even when the filesystem fails."""
# §AR-workspace.transport: Only synthetic reports and disposable files are used on the host.
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

PACKAGE = Path(__file__).resolve().parents[2]


class ReportStorage(unittest.TestCase):
    def publish(self, path, observed):
        result = subprocess.run(
            ['lake', 'env', 'lean', '--run', 'tests/integration/ReportStorage.lean',
             str(path), json.dumps(observed)],
            cwd=PACKAGE, capture_output=True, text=True, check=True, timeout=60)
        return json.loads(result.stdout)

    def test_successful_publication_is_retrievable(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'report.json'
            observed = dict(entry='yes', termination='exited', detail=7, cleanup='complete')
            result = self.publish(path, observed)
            self.assertEqual(json.loads(path.read_text()), result)
            self.assertEqual(result, dict(observed, report_storage='stored', report_storage_error=None))
            self.assertFalse(path.with_suffix('.json.tmp').exists())

    def test_missing_directory_preserves_setup_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'missing' / 'report.json'
            observed = dict(entry='no', termination='setup_failed', detail=5, cleanup='unknown')
            result = self.publish(path, observed)
            self.assertEqual({key: result[key] for key in observed}, observed)
            self.assertEqual(result['report_storage'], 'failed')
            self.assertTrue(result['report_storage_error'])
            self.assertFalse(path.exists())

    def test_publication_error_preserves_execution_and_cancellation(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'report.json'
            path.mkdir()
            observed = dict(entry='yes', termination='exited', detail=0,
                            cleanup='complete', cancellation_bits=1)
            result = self.publish(path, observed)
            self.assertEqual({key: result[key] for key in observed}, observed)
            self.assertEqual(result['report_storage'], 'failed')
            self.assertTrue(result['report_storage_error'])
            self.assertTrue(path.is_dir())
            self.assertFalse(path.with_suffix('.json.tmp').exists())


if __name__ == '__main__':
    unittest.main()
