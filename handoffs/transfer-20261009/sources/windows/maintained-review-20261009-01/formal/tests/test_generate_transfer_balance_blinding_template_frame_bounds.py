"""Renderer regressions only: mock ingress is not a source or proof receipt."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_balance_blinding_template_frame_bounds as renderer
from circuits.transfer_relation import RelationError


class FrameBoundsRendererTests(unittest.TestCase):
    def plan(self):
        stages = [dict(output=i, auxiliary=i + 1) for i in range(192708, 193210, 2)]
        return dict(canonical=dict(bit_start=22232, value=9, stages=stages,
                    chunks=[stages[i:i + 16] for i in range(0, len(stages), 16)]),
                    bounds=dict(constant_copy=200692, high_start=22738,
                    frames=[dict(before=dict(low=22484, high=193210))]))

    def render(self, plan):
        with patch.object(renderer.whole, 'plan', return_value=plan):
            return renderer.generate(None, None, None, None, None)

    def test_bounded_chunks_and_symbolic_windows(self):
        name, source = self.render(self.plan())
        self.assertEqual(name, 'RuntimeBalanceBlindingTemplateFrameBounds')
        self.assertEqual(source.count('ScalarRandomizerWriteBounds.writes_bounds'), 16)
        self.assertIn('GroupFixedWriteBounds.certified_writes_outside', source)
        self.assertIn('theorem preserves_prior', source)
        self.assertNotIn('RuntimeTransferEpk', source)
        self.assertEqual(source.count('#print axioms '), 5)

    def test_allocation_drift_rejected(self):
        base = self.plan()
        for record, key, value in [('canonical', 'bit_start', 22233),
                                   ('canonical', 'value', 2),
                                   ('bounds', 'constant_copy', 200693),
                                   ('bounds', 'high_start', 22739)]:
            plan = copy.deepcopy(base)
            plan[record][key] = value
            with self.subTest(key=key), self.assertRaises(RelationError):
                self.render(plan)

    def test_reordered_product_chunks_rejected(self):
        plan = self.plan()
        plan['canonical']['chunks'][0] = list(reversed(plan['canonical']['chunks'][0]))
        with self.assertRaises(RelationError):
            self.render(plan)


if __name__ == '__main__':
    unittest.main()
