"""Actual source validation is retained; mocks only check renderer behavior."""
import copy
import unittest
from circuits import generate_transfer_balance_final_add_current as generator
from circuits.transfer_relation import RelationError
from tests import test_generate_transfer_balance_final_add_soundness as fixtures


class CurrentFinalAddTests(unittest.TestCase):
    def test_both_proofs_share_source_rows_and_current_tactics(self):
        modules=generator.render_plan(fixtures.plan())
        self.assertEqual([name for name,_ in modules],
            ['RuntimeTransferBalanceFinalAddCompletion','RuntimeTransferBalanceFinalAddSoundness'])
        self.assertEqual([body.count('#print axioms ') for _,body in modules],[13,16])
        for _,body in modules:
            self.assertNotIn('simp only [signedPoint,blindedPoint,Group.cross]\n    ring',body)
        sound=modules[1][1]
        self.assertIn('simp only [Bool.or_eq_true] at checked',sound)
        self.assertNotIn('Bool.or_eq_true.mp',sound)

    def test_altered_physical_row_is_rejected(self):
        plan=copy.deepcopy(fixtures.plan())
        plan['selected_rows'][0]['b'][0][1]=f'{2:064x}'
        with self.assertRaises(RelationError):generator.render_plan(plan)

    def test_missing_parents_are_rejected(self):
        with self.assertRaises(RelationError):generator.generate_from_joint(*([None]*11))
