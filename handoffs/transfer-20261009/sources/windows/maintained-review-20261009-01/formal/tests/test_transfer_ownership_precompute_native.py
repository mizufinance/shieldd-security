"""Typed native precompute join fixtures, without runtime/kernel credit."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_precompute_native as generator
from circuits.transfer_relation import RelationError


def fixture():
    cones = dict(cones=[dict(role='formula0', inputs=['px', 'py']),
                        dict(role='formula4', inputs=['tx', 'ty', 'px', 'py'])],
                 observations=dict(px=('linear', ((1, 1),)), py=('linear', ((2, 1),)),
                                   tx=('linear', ((20, 1),)), ty=('linear', ((30, 1),))))
    plan = dict(point_groups=[dict(material_end=0, stage_end=2)],
                stages=[dict(quotient=20), dict(quotient=30)])
    return dict(metadata=dict(constant_copy=100)), {}, plan, cones


class NativePrecomputeTests(unittest.TestCase):
    def render(self, values):
        checked, extracted, plan, cones = values
        with patch.object(generator.double, 'generate', return_value=('RuntimeOwnershipWindow000Point0Completion', '')), \
                patch.object(generator.addition, 'generate', return_value=('RuntimeOwnershipWindow000Point1Completion', '')), \
                patch.object(generator.native, 'generate', return_value=('RuntimeOwnershipWindow000Point0CompletionNativeSeed', '')), \
                patch.object(generator.completion, 'window_plan', return_value=plan), \
                patch.object(generator.completion.owner, 'cone_certificates', return_value=cones):
            return generator.generate(checked, extracted)

    def test_native_seed_derives_incoming_curve_and_preserves_original_rows(self):
        name, source = self.render(fixture())
        self.assertEqual(name, 'RuntimeOwnershipWindow000NativePrecompute')
        self.assertEqual(source.count('#check @'), 3)
        self.assertEqual(source.count('#print axioms'), 3)
        self.assertIn('native_double_complete', source)
        self.assertIn('GroupCircuitOrder.run_outside', source)
        self.assertIn('firstRows.all', source)
        self.assertIn('model.onCurve', source)
        statement = source.split('theorem native_precompute_complete', 1)[1].split(' := by', 1)[0]
        self.assertIn('3 •', statement)
        self.assertNotIn('Valid', statement)
        self.assertNotIn('Satisfies base', statement)
        self.assertNotIn('(valid', statement)
        self.assertNotIn('(coordinates', statement)

    def test_exact_captured2base_base_link_required(self):
        for mutation in ('order', 'coefficient', 'output'):
            values = copy.deepcopy(fixture())
            if mutation == 'order': values[3]['cones'][1]['inputs'].reverse()
            elif mutation == 'coefficient': values[3]['observations']['tx'] = ('linear', ((20, 2),))
            else: values[2]['stages'][0]['quotient'] = 21
            with self.subTest(mutation=mutation), self.assertRaises(RelationError):
                self.render(values)


if __name__ == '__main__':
    unittest.main()
