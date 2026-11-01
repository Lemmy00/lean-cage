"""Tamper with disposable archived evidence; never invoke a proof build."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-controller.composition: Preserve the review checkpoint before promotion.
# §REQ-proof-integrity.provenance: Receipt integrity must not imply theorem acceptance.
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import check_receipts as check


class ReceiptIntegrity(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / 'repo'
        paths = [check.RECEIPT, check.SNAPSHOT['path']]
        paths += [value[0] for value in check.IDENTITIES.values()]
        paths += ['assurance/m4-parent-checkpoint-' + name + '-check.log'
                  for name in check.EXPECTED]
        for relative in paths:
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(check.ROOT / relative, path)
        self.receipt = json.loads((self.root / check.RECEIPT).read_text())

    def save(self):
        (self.root / check.RECEIPT).write_text(json.dumps(self.receipt))

    def reject(self, message):
        self.save()
        with self.assertRaisesRegex(check.IntegrityError, message):
            check.check(self.root)

    def test_original_archive_is_integrity_only(self):
        self.assertEqual(check.check(self.root), {
            'receipts': 6, 'integrity_only': True,
            'review_candidate': True, 'full_m4_complete': False})

    def test_changed_baseline(self):
        self.receipt['baseline_commit'] = '0' * 40
        self.reject('baseline_commit')

    def test_completion_flags_cannot_be_widened(self):
        for name in ['accepted_claims_changed', 'full_controller_complete', 'full_m4_complete']:
            with self.subTest(name=name):
                self.receipt[name] = True
                self.reject(name)
                self.receipt[name] = False

    def test_false_flags_cannot_be_numbers(self):
        self.receipt['full_m4_complete'] = 0
        self.reject('full_m4_complete')

    def test_status_cannot_claim_acceptance(self):
        self.receipt['status'] = 'accepted and fully verified'
        self.reject('status')

    def test_ci_scope_cannot_claim_the_m4_chain(self):
        self.receipt['baseline_ci']['scope'] = 'all M4 proofs'
        self.reject('CI scope')

    def test_missing_receipt(self):
        self.receipt['validation'].pop()
        self.reject('duplicate, missing or unexpected receipt')

    def test_duplicate_receipt(self):
        self.receipt['validation'][-1] = self.receipt['validation'][0]
        self.reject('duplicate, missing or unexpected receipt')

    def test_changed_command(self):
        self.receipt['validation'][0]['command'] = ['true']
        self.reject('command')

    def test_failed_receipt(self):
        self.receipt['validation'][0]['exit_code'] = 1
        self.reject('exit code')

    def test_changed_log_is_rejected(self):
        (self.root / self.receipt['validation'][0]['log']).write_text('fabricated success')
        self.reject('log bytes')

    def test_changed_log_and_receipt_hash_cannot_refresh_pin(self):
        record = self.receipt['validation'][0]
        raw = b'fabricated success'
        (self.root / record['log']).write_bytes(raw)
        record['log_sha256'] = hashlib.sha256(raw).hexdigest()
        self.reject('recorded log hash')

    def test_relabelled_log_path(self):
        self.receipt['validation'][0]['log'] = '../outside.log'
        self.reject('log path')

    def test_reader_rejects_noncanonical_paths(self):
        for path in ['/etc/passwd', '../outside', 'assurance/../outside',
                     'assurance//file', './assurance/file', 'assurance\\file', 'a\0b']:
            with self.subTest(path=path), self.assertRaises(check.IntegrityError):
                check.read(self.root, path)

    def test_symlink_cannot_escape_even_to_identical_bytes(self):
        record = self.receipt['validation'][0]
        path = self.root / record['log']
        outside = Path(self.temporary.name) / 'outside.log'
        shutil.copyfile(path, outside)
        path.unlink()
        path.symlink_to(outside)
        self.reject('escapes repository')

    def test_duplicate_json_keys(self):
        path = self.root / check.RECEIPT
        raw = path.read_text()
        path.write_text(raw.replace('"schema_version": 1',
                                    '"schema_version": 1, "schema_version": 1'))
        with self.assertRaisesRegex(check.IntegrityError, 'duplicate JSON key'):
            check.check(self.root)

    def test_changed_snapshot(self):
        path = self.root / check.SNAPSHOT['path']
        path.write_bytes(path.read_bytes() + b'tampered')
        self.reject('compressed snapshot')

    def test_missing_log_fails_closed(self):
        (self.root / self.receipt['validation'][0]['log']).unlink()
        self.reject('cannot read evidence')

    def test_ancillary_claims_and_limits_are_also_frozen(self):
        self.receipt['limits'] = ['All M4 obligations have been proved.']
        self.reject('complete archived receipt')

    def test_changed_plain_snapshot_hash(self):
        self.receipt['snapshot']['uncompressed_sha256'] = '0' * 64
        self.reject('snapshot identities')

    def test_changed_native_or_obligation_bytes(self):
        for path, _ in check.IDENTITIES.values():
            with self.subTest(path=path):
                original = (self.root / path).read_bytes()
                (self.root / path).write_bytes(original + b'changed')
                self.reject(path)
                (self.root / path).write_bytes(original)

    def test_changed_inventory_foundations_or_exports(self):
        for section, key, value in [
                ('candidate', 'rocq_theorem_records', 0),
                ('exports', 'numeric_plan', {'declarations': 0, 'sha256': '0' * 64})]:
            with self.subTest(section=section):
                original = self.receipt[section][key]
                self.receipt[section][key] = value
                self.reject('theorem_records|export identities')
                self.receipt[section][key] = original
        self.receipt['foundations'][0]['assumption_names'] = []
        self.reject('recorded foundations')


if __name__ == '__main__':
    unittest.main()
