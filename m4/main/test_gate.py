# §AR-m4-controller.main-inputs: Reject changed claims, provenance and unchecked proof adaptations.
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check
import frontend


class MainInputGateTests(unittest.TestCase):
    def test_incomplete_claims_rejected(self):
        records = {'rocq_declarations': [{'name': 'n', 'full_type': 'T'}],
                   'replayed_number_declarations': [{'name': 'old'}], 'function_identity': {'name': 'identity'}}
        changed = copy.deepcopy(records)
        changed['rocq_declarations'] = []
        with self.assertRaisesRegex(ValueError, 'statement/foundation'):
            check.validate_claims(records, changed)

    def test_changed_hypothesis_rejected(self):
        records = {'rocq_declarations': [{'full_type': 'forall m, owned m -> result m'}],
                   'replayed_number_declarations': [1], 'function_identity': {'type': 'same'}}
        changed = copy.deepcopy(records)
        changed['rocq_declarations'][0]['full_type'] = 'forall m, result m -> result m'
        with self.assertRaises(ValueError):
            check.validate_claims(records, changed)

    def test_changed_foundations_rejected(self):
        original = [{'name': 'LeanCageController.Source.run', 'assumption_names': []}]
        changed = [{'name': 'LeanCageMainNumber.Source.run', 'assumption_names': ['extra']}]
        with self.assertRaisesRegex(ValueError, 'beyond namespace'):
            check.validate_number_records(changed, original)

    def test_exact_namespace_replay_accepted(self):
        original = [{'name': 'LeanCageController.Source.run', 'full_type': 'LeanCageController.Input -> result'}]
        copied = [{'name': 'LeanCageMainNumber.Source.run', 'full_type': 'LeanCageMainNumber.Input -> result'}]
        check.validate_number_records(copied, original)

    def test_unchecked_proofs_rejected(self):
        for text in ['Theorem x : True. Admitted.', 'Unset Guard Checking. Theorem x : True.',
                     'Theorem x : True. exact (vm_cast_no_check I).']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                check.proof_names(text, 'Test.')

    def test_empty_inventory_rejected(self):
        with self.assertRaisesRegex(ValueError, 'empty or duplicate'):
            check.proof_names('Definition x := 0.', 'Test.')

    def test_unknown_identifier_adaptation_rejected(self):
        original = 'Module Info.\nDefinition _different : ident := $"different".\n'
        with self.assertRaisesRegex(ValueError, 'identifier adaptation'):
            frontend.number_adapter(original)

    def test_missing_function_rejected(self):
        with self.assertRaisesRegex(ValueError, 'missing or duplicate'):
            frontend.function('Definition unrelated := 0.', 'main')

    def test_truncated_headers_rejected(self):
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            frontend.header_inputs('# 0 "<built-in>"\n')

    def test_changed_header_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'header.h'
            path.write_text('old')
            identities = {str(path): frontend.digest(path)}
            path.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'header/source changed'):
                frontend.verify_inputs(identities)

    def test_negative_identity_acceptance_rejected(self):
        ast = 'Definition f_number := {|\n Econst_int (Int.repr 10) tint\n|}.\n'
        with tempfile.TemporaryDirectory() as folder, patch.object(check, 'WORK', Path(folder)), \
                patch.object(check.profile, 'run', return_value=type('Result', (), {'stdout': ''})()):
            with self.assertRaisesRegex(ValueError, 'kernel accepted'):
                check.negative_identity(ast, 'adapter')

    def test_negative_identity_unrelated_failure_rejected(self):
        ast = 'Definition f_number := {|\n Econst_int (Int.repr 10) tint\n|}.\n'
        bad = check.subprocess.CalledProcessError(1, ['rocq'], output='Error: missing dependency')
        with tempfile.TemporaryDirectory() as folder, patch.object(check, 'WORK', Path(folder)), \
                patch.object(check.profile, 'run', side_effect=[type('Result', (), {'stdout': ''})(), bad]):
            with self.assertRaisesRegex(ValueError, 'unexpected reason'):
                check.negative_identity(ast, 'adapter')


if __name__ == '__main__':
    unittest.main()
