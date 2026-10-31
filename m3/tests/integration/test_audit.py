"""Check complete theorem evidence, not names or source text alone."""
# §AR-workspace.proofs: Missing records, changed full types and forbidden axioms must fail closed.
import copy
import importlib.util
import json
from pathlib import Path
import unittest

PROJECT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('m3_audit_test', PROJECT / 'scripts/audit_m3.py')
AUDIT = importlib.util.module_from_spec(spec)
spec.loader.exec_module(AUDIT)

class Audit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads(AUDIT.MANIFEST.read_text())
        cls.declarations = cls.manifest['declarations']

    def test_complete_types_and_logical_foundations(self):
        AUDIT.M1.validate_declarations(self.declarations, self.declarations)
        self.assertTrue(set(self.manifest['claims']) <= {r['name'] for r in self.declarations})
        self.assertTrue({'LeanCageM3.reachable_unguarded_read', 'LeanCageM3.reachable_processes_safe',
                         'LeanCageM3.Filter.policy_filter_action'} <= set(self.manifest['claims']))

    def test_missing_duplicate_changed_type_and_non_theorem(self):
        variants = [self.declarations[1:], self.declarations + self.declarations[:1]]
        for key, value in [('type', 'False'), ('is_theorem', False), ('axioms', ['sorryAx'])]:
            changed = copy.deepcopy(self.declarations)
            changed[0][key] = value
            variants.append(changed)
        for changed in variants:
            with self.subTest(), self.assertRaises(AUDIT.M1.AuditError):
                AUDIT.M1.validate_declarations(self.declarations, changed)

    def test_declared_compiler_trust_and_custom_axioms_rejected(self):
        for name in ['sorryAx', 'Lean.ofReduceBool', 'M3UnreviewedIsolation']:
            forged = copy.deepcopy(self.declarations)
            forged[0]['axioms'] = [name]
            with self.subTest(name=name), self.assertRaises(AUDIT.M1.AuditError):
                AUDIT.M1.validate_declarations(forged, forged)

if __name__ == '__main__':
    unittest.main()
