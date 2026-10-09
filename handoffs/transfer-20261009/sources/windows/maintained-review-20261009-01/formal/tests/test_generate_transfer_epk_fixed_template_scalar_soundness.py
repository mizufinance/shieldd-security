"""Source refusal checks and audit of the folded-prefix soundness premises."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_epk_fixed_template_scalar_soundness as emit
from circuits.transfer_relation import RelationError


class ScalarSoundnessTests(unittest.TestCase):
    def fixture(self):
        return {'chunks': [{'metadata': {'window_start': i}} for i in range(0, 126, 16)],
                'bounds': {'constant_copy': 1000, 'high_start': 201},
                'loop': {'programs': list(range(126))}}

    def render(self, accepted):
        with patch.object(emit.full, 'plan', return_value=accepted):
            return emit.generate(b'parent', [], {}, {}, {}, 0)

    def test_prefix_coordinate_is_derived_from_rows(self):
        name, source = self.render(self.fixture())
        self.assertEqual(name, 'RuntimeTransferEpk0FixedTemplateScalarSoundness')
        header = source.split('theorem actual_native_sound', 1)[1].split(' :\n    GroupFixedCircuitCompletion.point', 1)[0]
        for forbidden in ('inputMeaning', 'nextMeaning', 'word :', 'outputMeaning', 'endpoint'):
            self.assertNotIn(forbidden, header)
        self.assertIn('RuntimeTransferEpk0FixedWindow000.rawRows ++', source)
        self.assertIn('RuntimeTransferEpk0FixedWindow000.actual_window_coordinates', source)

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
