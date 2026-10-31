#!/usr/bin/env python3
"""Evidence-boundary regressions; no host workloads or Linux effects."""
# §AR-m4-effects.gate: Reject stale bytes, statement/axiom drift and invented closure.
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('connection_gate', Path(__file__).with_name('check.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class EvidenceGate(unittest.TestCase):
    def setUp(self):
        self.claims = json.loads(gate.MANIFEST.read_text())
        self.obligations = json.loads(gate.OBLIGATIONS.read_text())

    def test_reviewed_inventory(self):
        gate.validate_claims(self.claims, self.claims)
        self.assertEqual([r['name'] for r in self.claims['rocq_declarations']], gate.declaration_names())

    def test_stale_source_and_path_escape(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'input').write_bytes(b'reviewed')
            record = {'input': hashlib.sha256(b'reviewed').hexdigest()}
            gate.verify_hashes(record, root)
            (root / 'input').write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'tampered'):
                gate.verify_hashes(record, root)
            for path in ['../outside', '/absolute']:
                with self.assertRaisesRegex(ValueError, 'non-project'):
                    gate.verify_hashes({path: '0' * 64}, root)

    def test_theorem_and_assumption_drift(self):
        for field in ['full_type', 'transitive_assumptions', 'assumption_names']:
            actual = copy.deepcopy(self.claims)
            actual['rocq_declarations'][0][field] = 'altered'
            with self.assertRaisesRegex(ValueError, 'inventory differs'):
                gate.validate_claims(self.claims, actual)
        actual = copy.deepcopy(self.claims)
        actual['lean_declarations'][0]['axioms'] = ['sorryAx']
        with self.assertRaisesRegex(ValueError, 'inventory differs'):
            gate.validate_claims(self.claims, actual)

    def test_missing_or_empty_proof(self):
        for key in ['rocq_declarations', 'lean_declarations']:
            for value in [[], self.claims[key][1:]]:
                actual = copy.deepcopy(self.claims)
                actual[key] = value
                with self.assertRaisesRegex(ValueError, 'inventory differs'):
                    gate.validate_claims(self.claims, actual)

    def test_all_original_obligations_present(self):
        gate.validate_obligations(self.obligations)
        self.assertEqual(len(self.obligations['obligations']), 16)

    def test_obligation_removal_or_duplicate(self):
        for duplicate in [False, True]:
            actual = copy.deepcopy(self.obligations)
            actual['obligations'].pop()
            if duplicate:
                actual['obligations'].append(actual['obligations'][0])
            with self.assertRaisesRegex(ValueError, 'correspondence obligation'):
                gate.validate_obligations(actual)

    def test_invented_completion(self):
        actual = copy.deepcopy(self.obligations)
        actual['m4_complete'] = True
        with self.assertRaisesRegex(ValueError, 'cannot complete'):
            gate.validate_obligations(actual)
        for field, value in [('status', 'proved'), ('closure_evidence', ['source hash'])]:
            actual = copy.deepcopy(self.obligations)
            actual['obligations'][0][field] = value
            with self.assertRaisesRegex(ValueError, 'unreviewed correspondence closure'):
                gate.validate_obligations(actual)


if __name__ == '__main__':
    unittest.main()
