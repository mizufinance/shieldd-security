"""Generator regressions; mock plans confer no source or kernel proof credit."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_balance_blinding_template_frame_bounds_current as renderer
from circuits.transfer_relation import RelationError


class WideFrameBoundsTests(unittest.TestCase):
    def plan(self):
        stages=[dict(output=i,auxiliary=i+1) for i in range(192708,193210,2)]
        return dict(canonical=dict(bit_start=22232,value=9,stages=stages,
                    chunks=[stages[i:i+16] for i in range(0,len(stages),16)]),
                    bounds=dict(constant_copy=200692,high_start=192708,
                    frames=[dict(before=dict(low=22484,high=193210))]),
                    loop=dict(programs=[None]*126))

    def render(self,plan):
        with patch.object(renderer.whole,'plan',return_value=plan):
            return renderer.generate_modules(None,None,None,None,None)

    def test_actual_origin_and_wider_certificate_are_distinct(self):
        modules=self.render(self.plan())
        self.assertEqual(len(modules),9)
        self.assertEqual(sum(source.count('#print axioms ') for _,source in modules),14)
        self.assertEqual(sum(source.count('private theorem bound') for _,source in modules),125)
        for _,source in modules[:8]:
            self.assertIn('GroupFixedCircuitBounds.Certified 22738 200692',source)
            self.assertIn('GroupFixedCircuitBounds.checkLocal 22738 200692',source)
        final=modules[-1][1]
        self.assertIn('TransferBalanceBlindingTemplateFrame.prefixProgram n',final)
        self.assertIn('ordinary_wide_bounds n',final)
        self.assertNotIn('have first := RuntimeBalanceBlindingWindow000TemplatePrefix.checked_bounds',final)

    def test_incorrect_source_origin_is_rejected(self):
        for origin in [22738,192707,192709]:
            plan=self.plan();plan['bounds']['high_start']=origin
            with self.subTest(origin=origin),self.assertRaises(RelationError):
                self.render(plan)

    def test_missing_window_is_rejected(self):
        plan=self.plan();plan['loop']['programs'].pop()
        with self.assertRaises(RelationError):self.render(plan)
