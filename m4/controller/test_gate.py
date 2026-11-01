"""Integrity regressions for the controller provenance and preservation gate."""
# §AR-m4-controller.extraction: Drift must fail before a reviewed claim is accepted.
import copy
import unittest

import check
from extract_number import ROOT, extract, identity


class ControllerIntegrity(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (ROOT / 'native/leancage_m3.c').read_text()
        cls.claims = check.read(ROOT / 'assurance/m4-frames-claims.json')
        cls.evidence = check.read(ROOT / 'assurance/m4-frames-evidence.json')
        cls.parent = {**cls.claims, **cls.evidence}

    def test_exact_source_is_retained(self):
        generated = extract(self.source)
        self.assertEqual(identity(self.source, generated)['name'], 'number')

    def test_changed_overflow_branch_is_rejected(self):
        generated = extract(self.source).replace('result>', 'result>=')
        with self.assertRaises(ValueError):
            identity(self.source, generated)

    def test_ambiguous_source_is_rejected(self):
        with self.assertRaises(ValueError):
            extract(self.source + '\nstatic int number(const char *s, uint64_t *v) { return 0; }\n')

    def test_missing_source_is_rejected(self):
        with self.assertRaises(ValueError):
            extract('static int unrelated(void) { return 0; }\n')

    def test_prior_theorem_cannot_disappear(self):
        changed = copy.deepcopy(self.parent)
        changed['rocq_declarations'].pop()
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, changed)

    def test_prior_compiled_identity_cannot_change(self):
        changed = copy.deepcopy(self.parent)
        changed['artifact_sha256']['proofs/FrameComplete.vo'] = '0' * 64
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, changed)

    def test_prior_imported_endpoint_cannot_change(self):
        changed = copy.deepcopy(self.parent)
        changed['imported_endpoint']['full_type'] = 'replacement : True'
        with self.assertRaises(ValueError):
            check.validate_parent(self.claims, self.evidence, changed)

    def test_new_theorem_foundation_cannot_change(self):
        expected = {'rocq_declarations': [{'name': 'result', 'full_type': 'forall n, n=n', 'assumption_names': []}]}
        changed = copy.deepcopy(expected)
        changed['rocq_declarations'][0]['assumption_names'] = ['new_assumption']
        with self.assertRaises(ValueError):
            check.validate_claims(expected, changed)


if __name__ == '__main__':
    unittest.main()
