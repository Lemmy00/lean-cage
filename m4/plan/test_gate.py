"""Regression checks for altered parent claims and a disconnected numeric export."""
# §AR-m4-controller.plan: Missing, changed or unsupported evidence must be rejected.
import copy
import json
from pathlib import Path
import tempfile
import unittest

import check


class Gate(unittest.TestCase):
    def setUp(self):
        self.claims = check.read(check.ROOT / 'assurance/m4-number-checkpoint-claims.json')
        self.evidence = check.read(check.ROOT / 'assurance/m4-number-checkpoint-evidence.json')
        self.actual = {**copy.deepcopy(self.evidence), 'rocq_declarations': copy.deepcopy(self.claims['rocq_declarations'])}

    def test_unchanged_native_checkpoint(self):
        check.validate_parent(self.claims, self.evidence, self.actual)

    def test_dropped_native_theorem(self):
        self.actual['rocq_declarations'].pop()
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, self.actual)

    def test_changed_native_assumption(self):
        self.actual['rocq_declarations'][0]['assumption_names'].append('invented')
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, self.actual)

    def test_changed_native_artifact(self):
        self.actual['artifact_sha256']['proofs/NumberSource.vo'] = '0' * 64
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, self.actual)

    def test_changed_frontend(self):
        self.actual['frontend']['frontend_sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, self.actual)

    def test_changed_frame_parent(self):
        self.actual['parent']['export_sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, self.actual)

    def export_fixture(self, *, name=None, kind='def', version='4.35.0'):
        rows = [{'meta': {'lean': {'version': version}}},
                {'in': 1, 'str': {'pre': 0, 'str': name or check.EXPORT_ROOT}},
                {kind: {'name': 1}}]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'export.ndjson'
            path.write_text('\n'.join(json.dumps(row) for row in rows) + '\n')
            return check.export_inventory(path)

    def test_missing_computational_root(self):
        with self.assertRaises(ValueError):
            self.export_fixture(name='Unrelated.parser')

    def test_axiom_in_computational_closure(self):
        with self.assertRaises(ValueError):
            self.export_fixture(kind='axiom')

    def test_wrong_lean_version(self):
        with self.assertRaises(ValueError):
            self.export_fixture(version='4.34.0')

    def test_replaced_imported_endpoint(self):
        original = {'rocq_declarations': ['record'], 'lean_declarations': ['record'],
                    'imported_endpoint': {'full_type': 'Nat -> List Nat -> Option Nat'},
                    'export_inventory': {'declarations': ['root']}}
        changed = copy.deepcopy(original)
        changed['imported_endpoint']['full_type'] = 'True'
        with self.assertRaises(ValueError):
            check.validate_claims(original, changed)


if __name__ == '__main__':
    unittest.main()
