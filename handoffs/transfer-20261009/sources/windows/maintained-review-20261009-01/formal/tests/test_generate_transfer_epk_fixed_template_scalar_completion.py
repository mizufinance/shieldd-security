"""Refuse incomplete scalar supports and inspect constructive premises."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_epk_fixed_template_scalar_completion as emit
from circuits.transfer_relation import RelationError


class ScalarCompletionTests(unittest.TestCase):
    def fixture(self):
        bits = [[2, i] for i in range(252)]
        observed = {(2, i): ((10000+i, 1),) for i in range(252)}
        return {'chunks': [{'metadata': {'window_start': i, 'bits': bits}, 'observed': observed.copy()}
                           for i in range(0, 126, 16)],
                'bounds': {'constant_copy': 1000, 'high_start': 201,
                           'frames': [{'bit_support': [10000 + 2*i, 10001 + 2*i]}
                                      for i in range(126)]},
                'scalar': {'bit_start': 10000}, 'loop': {'programs': list(range(126))}}

    def render(self, accepted):
        with patch.object(emit.full, 'plan', return_value=accepted):
            return emit.generate(b'parent', [], {}, {}, {}, 0)

    def test_constructor_derives_all_rows_and_output(self):
        name, source = self.render(self.fixture())
        self.assertEqual(name, 'RuntimeTransferEpk0FixedTemplateScalarCompletion')
        header = source.split('theorem actual_native_scalar_complete', 1)[1].split(' :\n    let firstAssignment', 1)[0]
        for forbidden in ('Satisfies', 'inputMeaning', 'endpoint', 'word :'):
            self.assertNotIn(forbidden, header)
        self.assertIn('RuntimeTransferEpk0FixedWindow000TemplatePrefix.actual_native_prefix', source)
        self.assertIn('RuntimeTransferEpk0FixedTemplateOrdinaryPrior.actual_native_complete_prior', source)

    def test_missing_or_foreign_bit_support_refused(self):
        for mutation in ('missing', 'foreign'):
            accepted = copy.deepcopy(self.fixture())
            if mutation == 'missing':
                del accepted['chunks'][-1]['observed'][(2, 251)]
            else:
                accepted['chunks'][-1]['observed'][(2, 251)] = ((10252, 1),)
            with self.subTest(mutation=mutation), self.assertRaisesRegex(RelationError, 'exact250'):
                self.render(accepted)

    def test_missing_window_refused(self):
        accepted = self.fixture()
        accepted['loop']['programs'].pop()
        with self.assertRaisesRegex(RelationError, 'eight-page126'):
            self.render(accepted)


if __name__ == '__main__':
    unittest.main()
