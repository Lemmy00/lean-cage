"""Exercise the actual M2 theorem environment and preservation of reviewed M1 statements."""
# §AR-lifecycle.proofs: The full theorem gate rejects forbidden axioms and statement drift.
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

PROJECT=Path(__file__).resolve().parents[3]
SPEC=importlib.util.spec_from_file_location('m2_audit',PROJECT/'scripts/audit_m2.py')
AUDIT=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(AUDIT)


class Audit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records=AUDIT.query_environment(names=sorted(AUDIT.modules()))
        cls.manifest=json.loads(AUDIT.MANIFEST.read_text())

    def test_every_module_theorem_matches(self):
        AUDIT.validate_inventory(self.manifest['declarations'],self.records,AUDIT.modules())

    def test_changed_package_toolchain_is_rejected_and_recorded(self):
        self.assertIn('m2/lean-toolchain',AUDIT.required_sources())
        with tempfile.TemporaryDirectory() as directory:
            package=Path(directory)
            (package/'lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
            with mock.patch.object(AUDIT,'PACKAGE',package), \
                 self.assertRaisesRegex(AUDIT.M1.AuditError,'M2 toolchain differs'):
                AUDIT.check_toolchain()

    def test_empty_or_missing_inventory_is_rejected(self):
        for records in ([],self.records[1:]):
            with self.assertRaises(AUDIT.M1.AuditError):
                AUDIT.validate_inventory(self.manifest['declarations'],records,AUDIT.modules())

    def test_changed_proposition_is_rejected(self):
        changed=copy.deepcopy(self.manifest['declarations']);changed[0]['type']='True'
        with self.assertRaises(AUDIT.M1.AuditError):AUDIT.validate_inventory(changed,self.records,AUDIT.modules())

    def test_forbidden_transitive_axiom_is_rejected(self):
        records=AUDIT.query_environment(declarations=['M2Bad.claim'],extra_source='''
namespace M2Bad
axiom unjustified : False
theorem claim : False := unjustified
end M2Bad
''')
        claim=next(r for r in records if 'name' in r)
        with self.assertRaisesRegex(AUDIT.M1.AuditError,'Forbidden transitive axioms'):
            AUDIT.M1.validate_declarations([claim],[claim])

    def test_m1_statements_and_axioms_preserved(self):
        baseline=json.loads(AUDIT.BASELINE.read_text())
        records=AUDIT.query_environment(names=sorted(baseline['modules']))
        AUDIT.validate_inventory(baseline['declarations'],records,baseline['modules'])


if __name__=='__main__':unittest.main()
