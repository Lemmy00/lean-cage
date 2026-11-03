"""Checked-environment reader controls for the actual recursive type package."""
# §AR-m4-routes.reporting.bridge: Inventory unsupported shapes must fail explicitly.
import unittest
import check


class CheckedInventoryTests(unittest.TestCase):
    def test_variant_and_empty(self):
        signature = 'Module T := Struct Variant Empty : SProp :=. Variant V : Type := a : V | b : V. End'
        self.assertEqual(check.compiled_names(signature, 'T'), ['T.Empty', 'T.V', 'T.a', 'T.b'])

    def test_primitive_record_self_binder(self):
        signature = ('Module T := Struct Record R : Type := mk { value : nat } as self. '
                     'Definition value : forall _ : R, nat. End')
        self.assertEqual(check.compiled_names(signature, 'T'), ['T.R', 'T.mk', 'T.value'])

    def test_mutual_pair(self):
        signature = 'Module T := Struct Inductive A : Type := a : B -> A with B : Type := b : A -> B. End'
        self.assertEqual(check.compiled_names(signature, 'T'), ['T.A', 'T.a', 'T.B', 'T.b'])

    def test_unsupported_or_truncated(self):
        for signature in [
            'Module T := Struct Module Hidden := Struct Definition x : nat. End. End',
            'Module T := Struct Definition x : ... End',
            'Module T := Struct Mystery x : nat. End',
            'Module T := Struct Definition x : nat. Definition x : nat. End',
        ]:
            with self.subTest(signature=signature), self.assertRaises(ValueError):
                check.compiled_names(signature, 'T')


if __name__ == '__main__':
    unittest.main()
