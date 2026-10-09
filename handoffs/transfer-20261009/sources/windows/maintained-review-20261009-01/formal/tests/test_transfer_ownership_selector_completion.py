"""Typed selector boundaries only; fixtures carry no runtime qualification."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_selector_completion as generator
from circuits.transfer_relation import RelationError
from tests.test_transfer_ownership_folded_window_curve import fixture as folded_fixture


def fixture():
    checked, extracted, plan, cones = folded_fixture()
    checked['windows'] = [checked['windows'][0], checked['windows'][0]]
    plan.update(window_index=1, point_groups=[dict(index=7, kind='add',
        formula_start=30, formula_count=6)])
    for index, cone in enumerate(cones['cones'], 34):
        cone['role'] = 'formula'+str(index)
    for index, column in ((6, 249), (7, 250)):
        cones['observations'][str(index)] = ('linear', ((column, 1),))
    return checked, extracted, plan, cones


class SelectorCompletionTests(unittest.TestCase):
    def render(self, values, offset=1):
        checked, extracted, plan, cones = values
        with patch.object(generator.completion, 'window_plan', return_value=plan), \
                patch.object(generator.completion.owner, 'cone_certificates', return_value=cones):
            return generator.generate(checked, extracted, offset)

    def test_exact_constructed_selector_and_independent_curve_inputs(self):
        name, source = self.render(fixture())
        self.assertEqual(name, 'RuntimeOwnershipWindow001Point7SelectorCompletion')
        self.assertEqual(source.count('#check @'), 2)
        self.assertEqual(source.count('#print axioms'), 2)
        self.assertIn('formula34_constructed', source)
        self.assertIn('formula35_constructed', source)
        self.assertIn('Group.window_onCurve', source)
        self.assertIn('def low : Linear := '+generator.linear(((249,1),)), source)
        self.assertIn('def high : Linear := '+generator.linear(((250,1),)), source)
        statement = source.split('theorem material_curve', 1)[1].split(' := by', 1)[0]
        self.assertIn('lowValue', statement)
        self.assertIn('baseValid', statement)
        self.assertIn('materialAssignment base', statement)
        self.assertNotIn('Satisfies base', statement)
        self.assertNotIn('selectedValue', statement)

    def test_refuses_changed_shared_roles_endpoint_or_group(self):
        for mutation in ('order', 'endpoint', 'count', 'index'):
            values = copy.deepcopy(fixture())
            if mutation == 'order':
                values[3]['cones'][1]['inputs'].reverse()
            elif mutation == 'endpoint':
                values[3]['observations']['sx'] = ('linear', ((70, 2),))
            elif mutation == 'count':
                values[2]['point_groups'][0]['formula_count'] = 4
            else:
                values[2]['point_groups'][0]['index'] = 6
            with self.subTest(mutation=mutation), self.assertRaises(RelationError):
                self.render(values)
        for offset in (True, -1, 2):
            with self.subTest(offset=offset), self.assertRaises(RelationError):
                self.render(fixture(), offset)


if __name__ == '__main__':
    unittest.main()
