"""Reject source adaptations that change literal values or alias relationships."""
# §AR-m4-routes.reporting.chain: Identifier adaptation precedes actual-source kernel replay.
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("reporting_identifier_source", ROOT / "verification/reporting/source.py")
SOURCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SOURCE)


def ast(literals, uses, temporaries=(1, 2), result_uses=(), result_slots=()):
    declarations = []
    for name, byte in literals:
        declarations.append(f"""Definition v___stringlit_{name} := {{|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr {byte}) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}}.
""")
    registrations = " :: ".join(f"(___stringlit_{name}, Gvar v___stringlit_{name})" for name, _ in literals)
    terms = " ".join(f"(Evar ___stringlit_{name} (tarray tschar 2))" for name in uses)
    temps = " ".join(f"(Etempvar _t'{name} tint)" for name in temporaries)
    result_terms = " ".join(f"(Evar __res__{name} (Tstruct _result noattr))" for name in result_uses)
    result_vars = " :: ".join(f"(__res__{name}, ({kind}))" for name, kind in result_slots)
    return "\n".join(declarations) + f"""Definition global_definitions := ({registrations} :: nil).
Definition f_main := {{|
  fn_vars := ({result_vars + ' :: ' if result_vars else ''}nil);
  fn_temps := nil;
  fn_body := Ssequence ({temps} {terms} {result_terms}) (Evar _capture tint)
|}}.
"""


class SourceIdentifierTests(unittest.TestCase):
    def setUp(self):
        self.proofs = patch.object(SOURCE, "proof_literals", return_value=set())
        self.proofs.start()
        self.addCleanup(self.proofs.stop)
        self.results = patch.object(SOURCE, "proof_results", return_value=set())
        self.results.start()
        self.addCleanup(self.results.stop)

    def test_value_preserving_bijection(self):
        before = ast([(1, 65), (2, 66)], [1, 2, 1])
        after = ast([(8, 65), (9, 66)], [8, 9, 8], (4, 5))
        self.assertEqual(SOURCE.renaming(before, after),
                         {"1": "4", "2": "5", "___stringlit_1": "___stringlit_8", "___stringlit_2": "___stringlit_9"})

    def test_literal_value_type_and_flags_are_checked(self):
        before = ast([(1, 65)], [1])
        valid = ast([(8, 65)], [8])
        for old, new in (("Int.repr 65", "Int.repr 66"), ("tarray tschar 2", "tarray tschar 3"),
                         ("gvar_readonly := true", "gvar_readonly := false"),
                         ("gvar_volatile := false", "gvar_volatile := true")):
            with self.subTest(new=new), self.assertRaises(ValueError):
                SOURCE.renaming(before, valid.replace(old, new, 1))

    def test_literal_alias_split_and_merge_are_rejected(self):
        for before, after in ((ast([(1, 65)], [1, 1]), ast([(8, 65), (9, 65)], [8, 9])),
                              (ast([(1, 65), (2, 65)], [1, 2]), ast([(8, 65)], [8, 8]))):
            with self.subTest(after=after), self.assertRaises(ValueError):
                SOURCE.renaming(before, after)

    def test_global_registration_cannot_alias_another_literal(self):
        before = ast([(1, 65), (2, 66)], [1, 2])
        after = ast([(8, 65), (9, 66)], [8, 9])
        after = after.replace("(___stringlit_8, Gvar v___stringlit_8)", "(___stringlit_8, Gvar v___stringlit_9)")
        with self.assertRaises(ValueError):
            SOURCE.renaming(before, after)

    def test_duplicate_registration_is_rejected(self):
        before = ast([(1, 65)], [1])
        after = ast([(8, 65)], [8]).replace("Gvar v___stringlit_8) :: nil", "Gvar v___stringlit_8) :: (___stringlit_8, Gvar v___stringlit_8) :: nil")
        with self.assertRaises(ValueError):
            SOURCE.renaming(before, after)

    def test_unmapped_proof_literal_keeps_its_distinct_identity(self):
        before = ast([(1, 65), (2, 65)], [1])
        after = ast([(2, 65)], [2])
        with patch.object(SOURCE, "proof_literals", return_value={"___stringlit_2"}), self.assertRaises(ValueError):
            SOURCE.renaming(before, after)

    def test_temporary_alias_change_is_rejected(self):
        before = ast([(1, 65)], [1], (1, 1))
        after = ast([(1, 65)], [1], (4, 5))
        with self.assertRaises(ValueError):
            SOURCE.renaming(before, after)

    def test_other_ast_changes_are_rejected(self):
        before = ast([(1, 65)], [1])
        with self.assertRaises(ValueError):
            SOURCE.renaming(before, before.replace("Ssequence", "Sifthenelse"))

    def test_registered_result_local_bijection(self):
        kind = "Tstruct _result noattr"
        before = ast([(1, 65)], [1], result_uses=(6, 7, 6), result_slots=((6, kind), (7, kind)))
        after = ast([(1, 65)], [1], result_uses=(7, 8, 7), result_slots=((6, kind), (7, kind), (8, kind)))
        self.assertEqual(SOURCE.renaming(before, after), {"__res__6": "__res__7", "__res__7": "__res__8"})

    def test_result_local_registration_type_and_aliases_are_checked(self):
        kind = "Tstruct _result noattr"
        before = ast([(1, 65)], [1], result_uses=(6, 6), result_slots=((6, kind),))
        valid = ast([(1, 65)], [1], result_uses=(7, 7), result_slots=((7, kind),))
        for bad in (valid.replace("fn_vars := ((__res__7,", "fn_vars := ((__res__8,"),
                    valid.replace("fn_vars := ((__res__7, (Tstruct _result noattr))",
                                  "fn_vars := ((__res__7, (Tstruct _other noattr))"),
                    ast([(1, 65)], [1], result_uses=(7, 8), result_slots=((7, kind), (8, kind)))):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                SOURCE.renaming(before, bad)
        split = ast([(1, 65)], [1], result_uses=(6, 7), result_slots=((6, kind), (7, kind)))
        with self.assertRaises(ValueError):
            SOURCE.renaming(split, valid)

    def test_unmapped_proof_result_keeps_its_distinct_identity(self):
        kind = "Tstruct _result noattr"
        before = ast([(1, 65)], [1], result_uses=(6,), result_slots=((6, kind), (7, kind)))
        after = ast([(1, 65)], [1], result_uses=(7,), result_slots=((7, kind),))
        with patch.object(SOURCE, "proof_results", return_value={"__res__7"}), self.assertRaises(ValueError):
            SOURCE.renaming(before, after)

    def test_replacements_are_simultaneous_and_cover_variable_names(self):
        mapping = {"1": "2", "2": "3", "___stringlit_1": "___stringlit_2", "___stringlit_2": "___stringlit_3"}
        self.assertEqual(SOURCE.adapt("_t'1 _t'2 ___stringlit_1 v___stringlit_2 unrelated___stringlit_1", mapping),
                         "_t'2 _t'3 ___stringlit_2 v___stringlit_3 unrelated___stringlit_1")
        self.assertEqual(SOURCE.adapt("__res__6 __res__7 unrelated__res__6", {"__res__6": "__res__7", "__res__7": "__res__8"}),
                         "__res__7 __res__8 unrelated__res__6")


if __name__ == "__main__":
    unittest.main()
