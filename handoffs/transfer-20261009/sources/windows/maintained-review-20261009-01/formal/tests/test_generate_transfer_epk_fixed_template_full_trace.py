"""Whole ordinary source boundary checks; no runtime or kernel qualification."""
import copy, unittest
from unittest.mock import patch
from circuits import generate_transfer_epk_fixed_template_full_trace as emit
from circuits.transfer_relation import RelationError


class FullTraceTests(unittest.TestCase):
    def fixture(self):
        return {'chunks': [{'metadata': {'window_start': i}} for i in range(0, 126, 16)],
                'bounds': {'constant_copy': 1000, 'high_start': 201},
                'loop': {'programs': list(range(126))}}

    def render(self, accepted):
        with patch.object(emit.full, 'plan', return_value=accepted):
            return emit.generate(b'parent', [], {}, {}, {}, 0)

    def test_native_conclusion_requires_all_named_page_predecessors(self):
        name, source = self.render(self.fixture())
        self.assertEqual(name, 'RuntimeTransferEpk0FixedTemplateOrdinaryTrace')
        for i in range(8):
            self.assertIn(f'import ShielddSecurity.RuntimeTransferEpk0FixedTemplatePage{i:02d}Trace', source)
            self.assertIn(f'import ShielddSecurity.RuntimeTransferEpk0FixedTemplatePage{i:02d}Join', source)
        self.assertIn('GroupFixedTemplatePages.certified_pages', source)
        header = source.split('theorem actual_native_complete', 1)[1].split(' :\n    let completed', 1)[0]
        self.assertNotIn('Satisfies', header)
        self.assertNotIn('endpoint', header)

    def test_missing_or_reordered_page_refused(self):
        for mutation in ('missing', 'reordered'):
            accepted = copy.deepcopy(self.fixture())
            if mutation == 'missing':
                accepted['chunks'].pop()
            else:
                accepted['chunks'][0], accepted['chunks'][1] = accepted['chunks'][1], accepted['chunks'][0]
            with self.subTest(mutation=mutation), self.assertRaisesRegex(RelationError, 'eight-page126'):
                self.render(accepted)

    def test_missing_window_refused(self):
        accepted = self.fixture()
        accepted['loop']['programs'].pop()
        with self.assertRaisesRegex(RelationError, 'eight-page126'):
            self.render(accepted)


if __name__ == '__main__':
    unittest.main()
