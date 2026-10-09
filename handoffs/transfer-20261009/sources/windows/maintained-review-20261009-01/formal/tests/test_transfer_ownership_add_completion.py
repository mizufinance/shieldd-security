"""Typed local addition fixtures, without runtime observation/kernel credit."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_add_completion as addition
from circuits import generate_transfer_ownership_double_completion as shared
from circuits.transfer_relation import RelationError
from tests.test_transfer_ownership_double_completion import fixture


def addition_fixture():
    checked, extracted, plan, cones = fixture()
    cones['observations'].update(qx=('linear', ((3, 1),)), qy=('linear', ((4, 1),)))
    for index, cone in enumerate(cones['cones'], 4):
        cone['role'] = 'formula' + str(index)
        cone['inputs'] += ['qx', 'qy']
    plan['point_groups'] = [dict(index=0), dict(index=1, kind='add', material_end=0, stage_end=2)]
    return checked, extracted, plan, cones


class AdditionCompletionTests(unittest.TestCase):
    def render(self, values):
        checked, extracted, plan, cones = values
        with patch.object(shared.completion, 'window_plan', return_value=plan), \
                patch.object(shared.completion.owner, 'cone_certificates', return_value=cones):
            return addition.generate(checked, extracted)

    def test_owned_materializations_then_curve_derived_quotients(self):
        name, source = self.render(addition_fixture())
        self.assertEqual(name, 'RuntimeOwnershipWindow000Point1Completion')
        self.assertEqual(source.count('#check @'), 7)
        self.assertEqual(source.count('#print axioms'), 7)
        self.assertIn('GroupQuotientPairCompletion.add_complete', source)
        self.assertIn('formula4_constructed', source)
        self.assertIn('formula7_constructed', source)
        self.assertIn('Group.denominators_nonzero', source)
        self.assertIn('rightPoint', source)
        statement = source.split('theorem actual_point_complete', 1)[1].split(' := by', 1)[0]
        self.assertIn('leftValid', statement)
        self.assertIn('rightValid', statement)
        self.assertNotIn('Satisfies base', statement)
        self.assertNotIn('Legal', statement)
        self.assertNotIn('denominatorValue', statement)

    def test_exact_shared_four_operand_lcs_and_coordinate_endpoints(self):
        for mutation in ('inputs', 'order', 'endpoint', 'point_kind', 'folded'):
            values = copy.deepcopy(addition_fixture())
            if mutation == 'inputs': values[3]['cones'][0]['inputs'].pop()
            elif mutation == 'order': values[3]['cones'][3]['inputs'].reverse()
            elif mutation == 'endpoint': values[2]['stages'][1]['denominator'] = ((0, 1),)
            elif mutation == 'point_kind': values[2]['point_groups'][1]['kind'] = 'double'
            else: values[2]['stages'][0]['kind'] = 'linear'
            with self.subTest(mutation=mutation), self.assertRaises(RelationError):
                self.render(values)

    def test_later_addition_uses_constructed_selector_curve_input(self):
        checked, extracted, plan, cones = addition_fixture()
        checked['windows'] = [None, None]
        plan['window_index'] = 1
        plan['point_groups'] = [dict(index=7, kind='add', formula_start=30,
            formula_count=6, material_end=0, stage_end=2)]
        for index, cone in enumerate(cones['cones'], 30):
            cone['role'] = 'formula' + str(index)
        with patch.object(shared.completion, 'window_plan', return_value=plan), \
                patch.object(shared.completion.owner, 'cone_certificates', return_value=cones):
            name, source = addition.generate_window_addition(checked, extracted, 1)
            self.assertEqual(name, 'RuntimeOwnershipWindow001Point7Completion')
            self.assertEqual(source.count('#check @'), 7)
            statement = source.split('theorem actual_point_complete', 1)[1].split(' := by', 1)[0]
            self.assertIn('(rightPoint (RuntimeOwnershipWindow001Point7Materializations.materialAssignment base))', statement)
            self.assertNotIn('(rightPoint base)', statement)
            self.assertNotIn('Satisfies base', statement)
            preservation = source.split('theorem input_preserved', 1)[1].split(' := by', 1)[0]
            self.assertNotIn('rightPoint', preservation)
            for offset in (True, -1, 2):
                with self.assertRaises(RelationError):
                    addition.generate_window_addition(checked, extracted, offset)


if __name__ == '__main__':
    unittest.main()
