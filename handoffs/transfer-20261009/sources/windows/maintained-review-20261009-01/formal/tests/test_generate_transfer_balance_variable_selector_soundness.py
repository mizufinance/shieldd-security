"""Source matching controls; these tests grant no runtime or kernel credit."""
import copy
import unittest
from circuits import generate_transfer_balance_variable_selector_soundness as generator
from circuits import transfer_balance_variable_completion as completion
from circuits.transfer_relation import RelationError
from tests.test_transfer_balance_variable_completion import accepted_fixture


class VariableSelectorSoundnessTests(unittest.TestCase):
    def test_arbitrary_assignment_and_source_native_bits(self):
        checked, extracted = accepted_fixture()
        name, source = generator.generate_window(checked, extracted, 0)
        self.assertTrue(name.endswith('SelectorSoundness'))
        self.assertIn('satisfied : Satisfies rho ', source)
        self.assertNotIn('materialAssignment', source)
        self.assertEqual(source.count('#print axioms '), 2)

    def test_changed_selector_endpoint_is_rejected(self):
        checked, extracted = accepted_fixture()
        plan = completion.window_plan(checked, extracted, 0, False)
        cones = completion.cone_certificates(checked, extracted, 0, False)
        changed = copy.deepcopy(cones)
        group = plan['point_groups'][-1]
        cone = next(c for c in changed['cones']
                    if c['role'] == 'formula' + str(group['formula_start'] + 4))
        original = changed['observations'][cone['output']]
        changed['observations'][cone['output']] = (original[0], ((0, 17),))
        bits = tuple(checked['derived'][v[1]] for v in checked['window_bits'][0])
        with self.assertRaises(RelationError):
            generator.render_selector(checked, plan, changed, 0, bits)
