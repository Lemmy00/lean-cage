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
from unittest.mock import patch

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

    def test_universal_source_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'WriteAll.source_write_all_body', 'WriteAll.actual_program_symbols',
            'WriteAll.write_all_prefix_safety', 'WriteAll.write_all_defined_prefix',
            'WriteAll.write_all_return_exact', 'WriteAll.write_all_success_exists',
            'WriteWitnesses.arbitrary_write_ownership',
            'WriteWitnesses.source_retries_then_success',
            'WriteWitnesses.source_short_write_then_success',
            'WriteWitnesses.source_error_return', 'WriteWitnesses.source_zero_return',
            'WriteWitnesses.source_wait_then_partial_loss',
        }.issubset(names))

    def test_omitted_proof_module_rejected(self):
        with patch.object(gate, 'MODULES', gate.MODULES[:-1]):
            with self.assertRaisesRegex(ValueError, 'every authored proof file'):
                gate.declaration_names()

    def test_preserved_claim_cannot_disappear(self):
        previous = json.loads(gate.BASELINE_CLAIMS.read_text())
        gate.validate_preserved_claims(previous, self.claims)
        for key in ['rocq_declarations', 'lean_declarations']:
            actual = copy.deepcopy(self.claims)
            old_name = previous[key][0]['name']
            actual[key] = [record for record in actual[key] if record['name'] != old_name]
            with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
                gate.validate_preserved_claims(previous, actual)

    def test_preserved_claim_cannot_change(self):
        previous = json.loads(gate.BASELINE_CLAIMS.read_text())
        for key, field in [('rocq_declarations', 'transitive_assumptions'),
                           ('lean_declarations', 'axioms')]:
            actual = copy.deepcopy(self.claims)
            old_name = previous[key][0]['name']
            record = next(record for record in actual[key] if record['name'] == old_name)
            record[field] = 'changed foundation'
            with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
                gate.validate_preserved_claims(previous, actual)

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

    def test_reporting_primitives_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'ErrorNumber.source_error_number_body', 'ErrorNumber.source_execution',
            'ErrorNumber.normalize_signed', 'ErrorNumber.normalize_range',
            'ErrorNumber.error_number_return_exact', 'ErrorNumber.error_number_defined_prefix',
            'ErrorNumber.error_number_all_prefixes', 'ErrorNumber.error_number_at_most_35_steps',
            'ErrorNumber.error_number_loss_every_prefix',
            'ErrorNumber.arbitrary_errno_source_witness',
            'Readers.reader_execution', 'Readers.reader_return_exact',
            'Readers.reader_all_prefixes', 'Readers.reader_defined_prefix',
            'Readers.reader_loss_every_prefix',
            'Readers.arbitrary_get32_input', 'Readers.arbitrary_get64_input',
        }.issubset(names))

    def test_preserved_artifacts_and_complete_extension(self):
        previous = {'IO.vo': 'old-proof'}
        extended = {**previous, 'Readers.vo': 'new-proof'}
        gate.validate_artifacts(previous, extended, subset=True)
        gate.validate_artifacts(extended, extended)
        for actual in [{'Readers.vo': 'new-proof'}, {**extended, 'IO.vo': 'changed-proof'}]:
            with self.assertRaisesRegex(ValueError, 'artifact identity differs'):
                gate.validate_artifacts(previous, actual, subset=True)
        with self.assertRaisesRegex(ValueError, 'artifact inventory differs'):
            gate.validate_artifacts(previous, extended)
        with self.assertRaisesRegex(ValueError, 'artifact identity differs'):
            gate.validate_artifacts({}, extended, subset=True)

    def test_all_write_loop_claims_preserved(self):
        previous = json.loads(gate.PRIMITIVES_BASELINE.read_text())
        self.assertEqual(len(previous['rocq_declarations']), 126)
        self.assertEqual(len(previous['lean_declarations']), 12)
        gate.validate_preserved_claims(previous, self.claims)
        for field in ['full_type', 'transitive_assumptions', 'assumption_names']:
            actual = copy.deepcopy(self.claims)
            record = next(r for r in actual['rocq_declarations']
                          if r['name'] == 'WriteAll.write_all_prefix_safety')
            record[field] = 'changed previously checked claim'
            with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
                gate.validate_preserved_claims(previous, actual)

    def test_truncated_statement_cannot_be_approved(self):
        actual = copy.deepcopy(self.claims)
        actual['rocq_declarations'][0]['full_type'] = 'forall x, ...'
        with self.assertRaisesRegex(ValueError, 'truncated Rocq statement'):
            gate.validate_claims(actual, actual)

    def test_writer_source_and_roundtrip_claims_present(self):
        names = {r['name'] for r in self.claims['rocq_declarations']}
        self.assertTrue({
            'StoreSteps.store_path_all', 'StoreSteps.store_path_defined_prefix',
            'StoreSteps.store_path_loss_every_prefix',
            'WriteBytes.byte_writes_permissions', 'WriteBytes.byte_writes_outside',
            'WriteBytes.byte_writes_content', 'WriteBytes.writer_prefix_content',
            'Writers.writer_execution', 'Writers.writer_return_exact',
            'Writers.writer_all_prefixes', 'Writers.writer_defined_prefix',
            'Writers.writer_loss_every_prefix', 'Writers.put32_first_byte_loss',
            'Writers.arbitrary_put32_input', 'Writers.arbitrary_put64_input',
            'Writers.arbitrary_unaligned_writer_inputs',
            'CodecRoundtrip.put_get32_word', 'CodecRoundtrip.put_get64_word',
            'CodecRoundtrip.put32_source_roundtrip', 'CodecRoundtrip.put64_source_roundtrip',
        }.issubset(names))

    def test_all_reporting_primitives_preserved(self):
        previous = json.loads(gate.WRITERS_BASELINE.read_text())
        self.assertEqual(len(previous['rocq_declarations']), 173)
        self.assertEqual(len(previous['lean_declarations']), 12)
        gate.validate_preserved_claims(previous, self.claims)
        actual = copy.deepcopy(self.claims)
        record = next(r for r in actual['rocq_declarations']
                      if r['name'] == 'Readers.reader_all_prefixes')
        record['full_type'] = 'weakened preserved reader claim'
        with self.assertRaisesRegex(ValueError, 'changed or disappeared'):
            gate.validate_preserved_claims(previous, actual)


if __name__ == '__main__':
    unittest.main()
