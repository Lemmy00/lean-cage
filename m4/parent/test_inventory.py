"""Exercise forms that escaped the inherited theorem-name regular expression."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-parent.audit: Inventory regressions cover hidden proofs and unsupported commands.
from pathlib import Path
import unittest
import inventory


class InventoryTests(unittest.TestCase):
    def test_supported_package(self):
        for path in Path(__file__).parent.glob('*.v'):
            with self.subTest(path=path.name):
                self.assertTrue(inventory.declarations(path.read_text(), 'Test.'))

    def test_definition_proof_cannot_hide(self):
        self.assertEqual(inventory.declarations(
            'Definition hidden : True := I.\nLemma visible : True. Proof. exact I. Qed.', 'T.'),
            ['T.hidden', 'T.visible'])

    def test_nested_comments_and_strings(self):
        self.assertEqual(inventory.declarations(
            '(* outer (* Qed. *) *) Definition text := "(*Lemma. ""X"" *)".\n'
            'Lemma ok : True. Proof. exact I. Qed.', ''), ['text', 'ok'])

    def test_unsupported_inventory_commands(self):
        declarations = [
            'Local Lemma hidden : True. Proof. exact I. Qed.',
            'Global Lemma hidden : True. Proof. exact I. Qed.',
            'Polymorphic Lemma hidden : True. Proof. exact I. Qed.',
            '#[local] Lemma hidden : True. Proof. exact I. Qed.',
            '#[universes(polymorphic)] Definition hidden : True := I.',
            'Module Secret. Lemma hidden : True. Proof. exact I. Qed. End Secret.',
            'Program Definition hidden : True := I.',
            'Definition hidden : True. Proof. exact I. Defined.',
            'Let hidden : True := I.',
            'Axioms hidden : False.',
            'Unset Guard Checking. Definition x := 0.',
            'Lemma hidden : True. Proof. admit. Qed.',
            'Lemma hidden : True. Proof. exact I. Abort.',
            'Lemma hidden : True. Proof. Definition extra : True := I. exact I. Qed.',
        ]
        for source in declarations:
            with self.subTest(source=source):
                with self.assertRaises(ValueError):
                    inventory.declarations(source, '')


if __name__ == '__main__':
    unittest.main()
