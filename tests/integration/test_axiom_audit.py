"""Exercise the audit against actual Lean declarations and deliberately bad evidence."""

# §AR-filter-decoder.checks: Reject unsafe assumptions, omitted claims, and statement drift.

import copy
import importlib.util
from pathlib import Path
import unittest
from unittest import mock


PROJECT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("leancage_audit", PROJECT / "scripts/audit_axioms.py")
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class AxiomAuditIntegration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.production = AUDIT.query_environment(modules=sorted(AUDIT.project_modules()))
        cls.declarations = [item for item in cls.production if "name" in item]
        cls.fixtures = AUDIT.query_environment(
            declarations=[
                "AxiomFixture.viaAxiom", "AxiomFixture.viaSorry", "AxiomFixture.viaCompiler",
                "LeanCage.Linux.Filter.decode",
            ],
            extra_source="""
namespace AxiomFixture
axiom externalAssumption : False
theorem viaAxiom : False := externalAssumption
theorem viaSorry : False := by sorry
theorem viaCompiler : 2 + 2 = 4 := by native_decide
end AxiomFixture
""",
        )

    def test_production_inventory_passes(self):
        AUDIT.validate_declarations(self.declarations, self.declarations)

    def test_transitive_forbidden_axioms_fail_even_when_manifest_lists_them(self):
        for record in self.fixtures[:3]:
            with self.subTest(declaration=record["name"]):
                self.assertTrue(record["is_theorem"])
                self.assertTrue(set(record["axioms"]) - AUDIT.LOGICAL_AXIOMS)
                with self.assertRaisesRegex(AUDIT.AuditError, "Forbidden transitive axioms"):
                    AUDIT.validate_declarations([record], [record])
        self.assertIn("sorryAx", self.fixtures[1]["axioms"])

    def test_non_theorem_fails(self):
        record = self.fixtures[3]
        with self.assertRaisesRegex(AUDIT.AuditError, "Not a theorem"):
            AUDIT.validate_declarations([record], [record])

    def test_missing_declaration_fails_in_lean(self):
        with self.assertRaisesRegex(AUDIT.AuditError, "Lean audit query failed"):
            AUDIT.query_environment(declarations=["LeanCage.Linux.Filter.noSuchClaim"])

    def test_unrecorded_theorem_fails(self):
        with self.assertRaisesRegex(AUDIT.AuditError, "inventory differs"):
            AUDIT.validate_declarations(self.declarations[1:], self.declarations)

    def test_changed_type_fails(self):
        expected = copy.deepcopy(self.declarations)
        expected[0]["type"] = "True"
        with self.assertRaisesRegex(AUDIT.AuditError, "Theorem type differs"):
            AUDIT.validate_declarations(expected, self.declarations)

    def test_unreviewed_logical_axiom_set_fails(self):
        expected = copy.deepcopy(self.declarations)
        expected[0]["axioms"] = sorted(set(expected[0]["axioms"]) ^ {"Classical.choice"})
        with self.assertRaisesRegex(AUDIT.AuditError, "Unreviewed axiom set"):
            AUDIT.validate_declarations(expected, self.declarations)

    def test_empty_or_duplicate_inventory_fails(self):
        with self.assertRaises(AUDIT.AuditError):
            AUDIT.validate_declarations([], [])
        with self.assertRaises(AUDIT.AuditError):
            AUDIT.validate_declarations(self.declarations * 2, self.declarations)

    def test_source_identity_drift_fails_before_build(self):
        changed = AUDIT.required_sources()
        changed["LeanCage/Linux/FilterDecoder.lean"] = "0" * 64
        with mock.patch.object(AUDIT, "required_sources", return_value=changed):
            with self.assertRaisesRegex(AUDIT.AuditError, "Source/dependency identities differ"):
                AUDIT.audit()


if __name__ == "__main__":
    unittest.main()
