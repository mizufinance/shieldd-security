"""Small source/row regressions; these fixtures confer no kernel proof credit."""
import copy
import unittest

from circuits import generate_transfer_signed_balance_soundness as generator
from circuits.transfer_relation import RelationError
from tests import test_transfer_signed_balance_completion as fixtures


class SignedBalanceSoundnessTests(unittest.TestCase):
    def setUp(self):
        fixture = fixtures.SignedBalanceCompletionTests()
        fixture.setUp()
        self.recipe = fixture.recipe

    def test_arbitrary_assignment_and_symbolic_bit_membership(self):
        name, source = generator.render_checked(self.recipe)
        self.assertEqual(name, 'RuntimeTransferSignedBalanceSoundness')
        declaration = source.split('theorem actual_rows_sound', 1)[1].split(' := by', 1)[0]
        self.assertIn('satisfied : Satisfies rho RuntimeTransferSignedBalanceCompletion.rawRows', declaration)
        for forbidden in ('completeAssignment', 'nativeAmounts', 'magnitudeBound', 'signValue'):
            self.assertNotIn(forbidden, declaration)
        self.assertIn('ScalarBooleanReflection.columns_value', source)
        self.assertIn('← RuntimeTransferSignedBalanceCompletion.boolean_identity', source)
        self.assertIn('Compiler.unoutline_rows_sound', source)
        self.assertEqual(source.count('#check @'), 5)
        self.assertEqual(source.count('#print axioms '), 5)
        self.assertNotRegex(source, r'\b(sorry|admit|native_decide)\b')

    def test_changed_signed_boundary_is_refused(self):
        changed = copy.deepcopy(self.recipe)
        target = next(row for row in changed['raw_rows']
                      if row['row'] == changed['roles']['signed.equation'])
        column, coefficient = target['a'][0]
        target['a'][0] = [column, f'{int(coefficient, 16) + 1:064x}']
        with self.assertRaises(RelationError):
            generator.render_checked(changed)

    def test_changed_product_source_is_refused(self):
        changed = copy.deepcopy(self.recipe)
        changed['product_left'] = [(changed['negative'], 3)]
        with self.assertRaises(RelationError):
            generator.render_checked(changed)


if __name__ == '__main__':
    unittest.main()
