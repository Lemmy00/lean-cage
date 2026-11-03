"""Reject drift before reusing foundation evidence, without invoking a build."""
# §AR-tooling.checks: Changed and newly discovered inputs invalidate cached gate reuse.
import contextlib
import importlib.util
import io
from pathlib import Path
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('foundation_inputs',
                                            ROOT / 'scripts/check_foundation_inputs.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class FoundationInputs(unittest.TestCase):
    def test_matching_inputs_need_no_build(self):
        with mock.patch('subprocess.run', side_effect=AssertionError('unexpected build')):
            with contextlib.redirect_stdout(io.StringIO()):
                CHECK.main()

    def test_each_package_rejects_changed_and_unrecorded_inputs(self):
        for audit in CHECK.audits():
            for name in ('docs/functional-spec/FS-assurance.md', 'unrecorded-input.py'):
                with self.subTest(manifest=audit.MANIFEST.name, path=name):
                    changed = audit.required_sources()
                    changed[name] = '0' * 64
                    with mock.patch.object(audit, 'required_sources', return_value=changed):
                        with self.assertRaises(ValueError) as result:
                            CHECK.check_sources(audit)
                    self.assertIn(name, str(result.exception))


if __name__ == '__main__':
    unittest.main()
