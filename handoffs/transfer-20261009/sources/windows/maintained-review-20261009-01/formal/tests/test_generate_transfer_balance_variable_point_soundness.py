"""Source-matching fixtures validate generation, not runtime or kernel claims."""
import copy
import unittest
from circuits import generate_transfer_balance_variable_point_soundness as generator
from circuits import transfer_balance_variable_completion as completion
from circuits.transfer_relation import RelationError
from tests.test_transfer_balance_variable_completion import accepted_fixture


class VariablePointSoundnessTests(unittest.TestCase):
    def test_arbitrary_assignment_for_all_three_point_operations(self):
        checked,extracted=accepted_fixture()
        modules=generator.generate_window(checked,extracted,0)
        self.assertEqual(len(modules),3)
        for name,source in modules:
            self.assertTrue(name.endswith('Soundness'))
            self.assertEqual(source.count('#print axioms '),7)
            statement=source.split('theorem actual_point_sound',1)[1].split(' := by',1)[0]
            self.assertIn('satisfied : Satisfies rho rawRows',statement)
            self.assertNotIn('completeAssignment',statement)
            self.assertIn('GroupQuotientRowSoundness.product_equation',source)
            self.assertIn('Compiler.checked_row_sound',source)
            self.assertNotIn('Bool.or_eq_true.mp',source)

    def test_changed_quotient_formula_endpoint_is_rejected(self):
        checked,extracted=accepted_fixture()
        plan=completion.window_plan(checked,extracted,0,False)
        cones=completion.cone_certificates(checked,extracted,0,False)
        group=plan['point_groups'][0]
        changed=copy.deepcopy(plan)
        changed['stages'][group['material_end']]['numerator']=((0,17),)
        with self.assertRaises(RelationError):
            generator.render_point(checked,extracted,changed,cones,group['index'])

    def test_precompute_keeps_exact_source_operation_order(self):
        checked,extracted=accepted_fixture()
        modules=generator.generate_precompute(checked,extracted)
        self.assertEqual(len(modules),2)
        self.assertTrue(modules[0][0].endswith('Point0Soundness'))
        self.assertTrue(modules[1][0].endswith('Point1Soundness'))
