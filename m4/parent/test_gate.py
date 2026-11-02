"""Tamper the concrete reviewed statement and artifact records."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-parent.audit: A matching source hash cannot replace complete evidence checks.
import copy
import hashlib
from pathlib import Path
import tempfile
import unittest
import check


@unittest.skipUnless(check.MANIFEST.is_file(), 'initial statement collection precedes reviewed expectations')
class ParentEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.expected = check.read(check.MANIFEST)
        self.actual = copy.deepcopy(self.expected)

    def test_unchanged_statements(self):
        check.validate_claims(self.expected, self.actual)

    def test_missing_statement(self):
        self.actual['rocq_declarations'].pop()
        with self.assertRaises(ValueError):
            check.validate_claims(self.expected, self.actual)

    def test_missing_generated_statement_in_both_records(self):
        for record in [self.expected, self.actual]:
            record['rocq_declarations'] = [row for row in record['rocq_declarations']
                                         if not row['name'].endswith('.trace_certificate_ind')]
        with self.assertRaises(ValueError):
            check.validate_claims(self.expected, self.actual)

    def test_missing_frontier_contract_in_both_records(self):
        for record in [self.expected, self.actual]:
            record['primary_contracts'] = [name for name in record['primary_contracts']
                                          if not name.endswith('.trace_post_bounds_cut')]
        with self.assertRaises(ValueError):
            check.validate_claims(self.expected, self.actual)

    def test_duplicate_statement(self):
        self.actual['rocq_declarations'].append(self.actual['rocq_declarations'][0])
        with self.assertRaises(ValueError):
            check.validate_claims(self.expected, self.actual)

    def test_missing_contract_in_both_records(self):
        for record in [self.expected, self.actual]:
            record['rocq_declarations'] = [row for row in record['rocq_declarations']
                                         if not row['name'].endswith('.matching_history')]
        with self.assertRaises(ValueError):
            check.validate_claims(self.expected, self.actual)

    def test_changed_transitive_foundation(self):
        self.actual['rocq_declarations'][0]['assumption_names'].append('unreviewed_os_axiom')
        with self.assertRaises(ValueError):
            check.validate_claims(self.expected, self.actual)

    def test_unreviewed_candidate_change_even_in_both_records(self):
        for record in [self.expected, self.actual]:
            row = next(row for row in record['rocq_declarations']
                       if row['name'].endswith('.parent_live_progress'))
            row['full_type'] += ' weaker'
        with self.assertRaises(ValueError):
            check.validate_claims(self.expected, self.actual)

    def test_fabricated_history(self):
        row = next(row for row in self.actual['rocq_declarations']
                   if row['name'].endswith('.trace_execution_split'))
        changed = row['full_type'].replace('observations', 'fabricated_history')
        self.assertNotEqual(changed, row['full_type'])
        row['full_type'] = changed
        with self.assertRaises(ValueError):
            check.validate_claims(self.expected, self.actual)

    def test_lost_input_representation(self):
        row = next(row for row in self.actual['rocq_declarations']
                   if row['name'].endswith('.allocated_validation_matching'))
        changed = row['full_type'].replace('validation_input_representation', 'erased_input_relation')
        self.assertNotEqual(changed, row['full_type'])
        row['full_type'] = changed
        with self.assertRaises(ValueError):
            check.validate_claims(self.expected, self.actual)

    def test_changed_imported_computation(self):
        self.actual['imported_endpoint']['full_type'] += ' unreviewed'
        with self.assertRaises(ValueError):
            check.validate_claims(self.expected, self.actual)


@unittest.skipUnless(check.EVIDENCE.is_file(), 'initial evidence collection precedes reviewed expectations')
class ParentIdentityTests(unittest.TestCase):
    def setUp(self):
        self.evidence = check.read(check.EVIDENCE)
        self.actual = copy.deepcopy(self.evidence)
        self.archive = copy.deepcopy(self.evidence)

    def test_unchanged_identities(self):
        check.validate_evidence(self.evidence, self.archive, self.actual, check.digest(check.MANIFEST))

    def test_altered_identity(self):
        for key in ['source_sha256', 'baseline', 'exports', 'artifact_sha256', 'kernel_output']:
            with self.subTest(field=key):
                actual = copy.deepcopy(self.actual)
                actual[key] = 'tampered'
                with self.assertRaises(ValueError):
                    check.validate_evidence(self.evidence, self.archive, actual, check.digest(check.MANIFEST))

    def test_tampered_archive(self):
        self.archive['artifact_sha256'] = {}
        with self.assertRaises(ValueError):
            check.validate_evidence(self.evidence, self.archive, self.actual, check.digest(check.MANIFEST))

    def test_tampered_claim_receipt(self):
        self.evidence['claims_sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            check.validate_evidence(self.evidence, self.archive, self.actual, check.digest(check.MANIFEST))

    def test_false_completion(self):
        for field in ['full_controller_complete', 'full_m4_complete']:
            with self.subTest(field=field):
                actual = copy.deepcopy(self.actual)
                actual[field] = True
                with self.assertRaises(ValueError):
                    check.validate_evidence(self.evidence, self.archive, actual, check.digest(check.MANIFEST))

    def test_status_receipt_tampering(self):
        self.evidence['status'] = 'accepted full M4'
        with self.assertRaises(ValueError):
            check.validate_evidence(self.evidence, self.archive, self.actual, check.digest(check.MANIFEST))

    def test_missing_receipt_inventory(self):
        self.evidence['archived_receipts_sha256'] = {}
        with self.assertRaises(ValueError):
            check.validate_evidence(self.evidence, self.archive, self.actual, check.digest(check.MANIFEST))

    def test_extra_receipt_inventory(self):
        self.evidence['archived_receipts_sha256']['invented.log'] = '0' * 64
        with self.assertRaises(ValueError):
            check.validate_evidence(self.evidence, self.archive, self.actual, check.digest(check.MANIFEST))

    def test_altered_original_receipt_identity(self):
        self.evidence['archived_receipts_sha256']['assurance/m4-parent-checkpoint-validation.json'] = '0' * 64
        with self.assertRaises(ValueError):
            check.validate_evidence(self.evidence, self.archive, self.actual, check.digest(check.MANIFEST))

    def test_receipt_content_tampering(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            log = root / 'receipt.log'
            log.write_bytes(b'kernel replay passed\n')
            expected = {'receipt.log': hashlib.sha256(log.read_bytes()).hexdigest()}
            check.bridge.connection().verify_hashes(expected, root)
            log.write_bytes(b'fabricated receipt\n')
            with self.assertRaises(ValueError):
                check.bridge.connection().verify_hashes(expected, root)


if __name__ == '__main__':
    unittest.main()
