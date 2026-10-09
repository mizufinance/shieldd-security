"""Small formula renderer regressions; no runtime capture or kernel proof credit."""
import copy
import unittest
from circuits import generate_transfer_balance_final_add_soundness as generator
from circuits import transfer_balance_shared_add as shared
from circuits.transfer_relation import RelationError
from tests.test_transfer_balance_shared_add import fixture


def plan():
    roles, rows, identity = fixture()
    matcher = shared.Matcher(roles)
    for row in rows:
        matcher.observe(row)
    return matcher.finish(identity)


class FinalAddSoundnessTests(unittest.TestCase):
    def test_derives_endpoint_from_actual_assignment_rows(self):
        name, source = generator.render_plan(plan())
        self.assertEqual(name, 'RuntimeTransferBalanceFinalAddSoundness')
        statement = source.split('theorem actual_rows_sound', 1)[1].split(' := by', 1)[0]
        self.assertIn('satisfied : Satisfies rho rawRows', statement)
        self.assertNotIn('completeAssignment', statement)
        self.assertNotIn('expectedRows', statement)
        self.assertNotIn('Group.OnCurve', statement)
        self.assertIn('Compiler.unoutline_rows_sound', source)
        self.assertIn('Compiler.checked_row_sound', source)
        self.assertIn('scaleLinear (-1) row.a', source)
        self.assertEqual(source.count('#print axioms '), 16)
        self.assertEqual(source.count('#check @'), 16)

    def test_changed_captured_row_refused_by_recheck(self):
        changed = copy.deepcopy(plan())
        changed['selected_rows'][0]['b'][0][1] = f'{2:064x}'
        with self.assertRaises(RelationError):
            generator.render_plan(changed)

    def test_missing_genuine_parent_or_shared_lowering_refused(self):
        with self.assertRaises(RelationError):
            generator.generate_from_joint(*([None] * 11))
        with self.assertRaises(RelationError):
            generator.render_plan({'lowering': 'two_independent_quotients'})


if __name__ == '__main__':
    unittest.main()
