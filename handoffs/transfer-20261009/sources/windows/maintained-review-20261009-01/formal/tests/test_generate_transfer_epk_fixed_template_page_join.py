"""Source read-frame refusals; fixtures confer no runtime or Lean credit."""
import copy, unittest
from unittest.mock import patch
from circuits import generate_transfer_epk_fixed_template_page_join as emit
from circuits.transfer_relation import RelationError
from tests.test_generate_transfer_epk_fixed_template_trace_page import TemplateTracePageTests


class PageJoinTests(unittest.TestCase):
    def fixture(self):
        selection, accepted = TemplateTracePageTests().fixture()
        accepted['loop'] = {'kept': [0, 1, 2, 11, 12, 1000]}
        layout = emit.template._layout(selection[0], selection[1], selection[2], selection[5], 0)
        return selection, accepted, layout

    def render(self, selection, accepted, layouts):
        with patch.object(emit.full, 'plan', return_value=accepted), \
             patch.object(emit.ingress, '_selection', return_value=selection), \
             patch.object(emit.template, '_layout', side_effect=layouts):
            return emit.generate(b'parent', [], {}, {}, {'fixed': {}}, 0, 1)

    def test_carries_first_ordinary_input_on_later_page(self):
        selection, accepted, layout = self.fixture()
        name, source = self.render(selection, accepted, [layout, layout])
        self.assertEqual(name, 'RuntimeTransferEpk0FixedTemplatePage01Join')
        self.assertIn('def incomingKept : List Nat := [30, 31]', source)
        self.assertIn('GroupFixedCircuitCompletion.Protected incomingKept', source)
        self.assertIn('GroupFixedReadIntervals.protected_reads', source)

    def test_global_caller_write_alias_refused(self):
        selection, accepted, layout = self.fixture()
        accepted['loop']['kept'].append(60)
        selection[5]['kept'].append(60)
        with self.assertRaisesRegex(RelationError, 'writes alias'):
            self.render(selection, accepted, [layout, layout])

    def test_first_input_write_alias_refused(self):
        selection, accepted, layout = self.fixture()
        initial = copy.deepcopy(layout)
        initial['before'] = (((60, 1),), ((31, 1),))
        with self.assertRaisesRegex(RelationError, 'writes alias'):
            self.render(selection, accepted, [initial, layout])

    def test_foreign_scope_read_gets_explicit_interval_protection(self):
        selection, accepted, layout = self.fixture()
        accepted['loop']['kept'].append(99)
        _, source = self.render(selection, accepted, [layout, layout])
        self.assertIn('def commonBlock0 : List Nat := [0, 1, 2, 11, 12, 99, 1000]', source)
        self.assertIn('theorem common_outside', source)
        self.assertNotIn('decide (column ∈', source)

    def test_read_inside_write_region_requires_a_narrower_certificate(self):
        selection, accepted, layout = self.fixture()
        layout = copy.deepcopy(layout)
        layout['stages'][0]['auxiliary'] = 400
        accepted['loop']['kept'].append(300)
        with self.assertRaisesRegex(RelationError, 'crosses actual write region'):
            self.render(selection, accepted, [layout, layout])


if __name__ == '__main__':
    unittest.main()
