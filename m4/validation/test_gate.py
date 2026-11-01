"""Reject changed source identities, proof obligations and computational exports."""
# §AR-m4-controller.strings: Keep altered or incomplete evidence out of the maintained gate.
import copy
import json
from pathlib import Path
import tempfile
import unittest

import check


class Gate(unittest.TestCase):
    def setUp(self):
        self.claims = check.read(check.ROOT / 'assurance/m4-digest-checkpoint-claims.json')
        self.evidence = check.read(check.ROOT / 'assurance/m4-digest-checkpoint-evidence.json')
        self.actual = {**copy.deepcopy(self.evidence), **copy.deepcopy(self.claims)}

    def test_preserved_digest_checkpoint(self):
        check.validate_parent(self.claims, self.evidence, self.actual)

    def test_dropped_digest_statement(self):
        self.actual['rocq_declarations'].pop()
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, self.actual)

    def test_changed_digest_assumption(self):
        self.actual['rocq_declarations'][0]['assumption_names'].append('invented')
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, self.actual)

    def test_weakened_digest_statement(self):
        self.actual['rocq_declarations'][0]['full_type'] = 'True'
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, self.actual)

    def test_changed_compiled_parent(self):
        self.actual['artifact_sha256']['proofs/DigestSource.vo'] = '0' * 64
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, self.actual)

    def test_changed_parent_export(self):
        self.actual['export_sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, self.actual)

    def export_fixture(self, *, extra=None, root=None, version='4.35.0'):
        rows = [{'meta': {'lean': {'version': version}}},
                {'in': 1, 'str': {'pre': 0, 'str': root or check.EXPORT_ROOT}}, {'def': {'name': 1}}]
        if extra:
            rows += [{'in': 2, 'str': {'pre': 0, 'str': extra[0]}}, {extra[1]: {'name': 2}}]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'export.ndjson'
            path.write_text('\n'.join(json.dumps(row) for row in rows) + '\n')
            return check.export_inventory(path)

    def test_missing_actual_root(self):
        with self.assertRaises(ValueError):
            self.export_fixture(root='Unrelated.digest')

    def test_new_computational_axiom(self):
        with self.assertRaises(ValueError):
            self.export_fixture(extra=('invented', 'axiom'))

    def test_unreviewed_modulus_closure(self):
        for name in ['Nat.mod', 'String.toUTF8', 'Array.get', 'UInt8.toNat']:
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.export_fixture(extra=(name, 'def'))

    def test_changed_lean_pin(self):
        with self.assertRaises(ValueError):
            self.export_fixture(version='4.34.0')

    def test_weakened_imported_endpoint(self):
        expected = {'rocq_declarations': ['source'], 'lean_declarations': ['live'],
                    'imported_endpoint': {'full_type': 'List Nat -> Bool'},
                    'export_inventory': {'declarations': ['root']}}
        actual = copy.deepcopy(expected)
        actual['imported_endpoint']['full_type'] = 'True'
        with self.assertRaises(ValueError):
            check.validate_claims(expected, actual)

    def test_unfinished_or_unchecked_proof(self):
        for text in ['Lemma x : True. Admitted.', 'Unset Guard Checking. Lemma x : True. Proof. exact I. Qed.',
                     'Lemma x : True. Proof. vm_cast_no_check I. Qed.']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                check.proof_names(text, 'Rejected.')


if __name__ == '__main__':
    unittest.main()
