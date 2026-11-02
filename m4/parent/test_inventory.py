"""Exercise forms that escaped the inherited theorem-name regular expression."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-parent.audit: Inventory regressions cover hidden proofs and unsupported commands.
from pathlib import Path
import unittest
import tempfile
import inventory
import check


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
            'Fixpoint visible (n:nat):True := match n with O=>I | S n=>hidden n end '
            'with hidden (n:nat):True := match n with O=>I | S n=>visible n end.',
            'Lemma visible:True. Proof. Time Definition hidden:True:=I. exact hidden. Qed.',
        ]
        for source in declarations:
            with self.subTest(source=source):
                with self.assertRaises(ValueError):
                    inventory.declarations(source, '')

    def test_unsupported_checked_signatures(self):
        for signature in [
                'Module T := Struct Module Hidden := Struct Definition x : True. End End',
                'Module T := Struct Definition x : ... . End',
                'Module T := Struct Definition x : (True. End',
                'Module T := Struct Inductive t : Set := c : t with u : Set := d : u. End',
                'Module T := Struct Definition x : True. Definition x : True. End']:
            with self.subTest(signature=signature), self.assertRaises(ValueError):
                inventory.checked_declarations(signature, 'Test.T')

    def test_compiled_hidden_declarations(self):
        """Both review counterexamples and Local proofs must appear in the environment."""
        cases = [
            ('Mutual', 'Fixpoint visible (n:nat):True := '
             'match n with O=>I | S n=>hidden n end '
             'with hidden (n:nat):True := match n with O=>I | S n=>visible n end.',
             {'visible', 'hidden'}),
            ('Nested', 'Lemma visible:True. Proof. '
             'Time Definition hidden:True:=I. exact hidden. Qed.', {'visible', 'hidden'}),
            ('Local', 'Local Definition hidden:True:=I. Lemma visible:True. Proof. exact hidden. Qed.',
             {'hidden', 'visible'}),
            ('Generated', 'Inductive tag := left_tag | right_tag. '
             'Record pair := { first:tag; second:tag }.',
             {'tag', 'left_tag', 'right_tag', 'tag_rect', 'tag_ind', 'tag_rec', 'tag_sind',
              'pair', 'Build_pair', 'first', 'second'}),
        ]
        check.WORK.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='inventory-controls-', dir=check.WORK) as directory:
            root = Path(directory)
            options = ['-Q', str(root), 'InventoryControl']
            for module, source, expected in cases:
                with self.subTest(module=module):
                    path = root / (module + '.v')
                    path.write_text(source + '\n')
                    check.profile.run(['rocq', 'c', '-q', *options, str(path)], cwd=root)
                    query = root / 'Query.v'
                    query.write_text('From InventoryControl Require Import ' + module + '.\n'
                                     'Set Printing All.\nSet Printing Depth 1000000.\n'
                                     'Set Printing Width 1000000.\n'
                                     'Print Module InventoryControl.' + module + '.\n')
                    output = check.profile.run(['rocq', 'c', '-q', *options, str(query)], cwd=root).stdout
                    actual = inventory.checked_declarations(output, 'InventoryControl.' + module)
                    self.assertEqual(set(actual), {'InventoryControl.' + module + '.' + name
                                                   for name in expected})


if __name__ == '__main__':
    unittest.main()
