"""H renderer regressions only; fixtures bypass ingress and grant no proof credit."""
import copy
import unittest
from unittest.mock import patch

from circuits import generate_transfer_balance_blinding_template_ordinary_soundness as sound
from circuits import generate_transfer_balance_blinding_template_scalar_completion as complete
from circuits import generate_transfer_balance_blinding_template_canonical_ingress as ingress
from circuits import generate_transfer_balance_blinding_template_canonical_preservation as preserve
from circuits import generate_transfer_balance_blinding_template_canonical_soundness as canonical_sound
from circuits.transfer_relation import RelationError


class BlindingTemplateCompositionTests(unittest.TestCase):
    def fixture(self):
        bits = [[0, i] for i in range(252)]
        expressions = {(0, i): ((22232 + i, 1),) for i in range(252)}
        return {
            'checked': {'chunks': [
                {'metadata': {'window_start': i, 'bits': bits}, 'expressions': expressions}
                for i in range(0, 126, 16)]},
            'loop': {'programs': list(range(126))},
            'bounds': {'constant_copy': 200692, 'high_start': 88620,
                       'frames': [{'before': {'low': 22484, 'high': 193210},
                                   'after': {'low': 22486, 'high': 193214}}] * 126},
            'canonical': {'bit_start': 22232, 'value': 9},
        }

    def render(self, renderer, fixture, page=None):
        with patch.object(renderer.whole, 'plan', return_value=fixture):
            if page is None:
                return renderer.generate(b'parent', [], [], [], {})
            return renderer.generate_modules(b'parent', [], [], [], {}, page)

    def test_soundness_initializes_actual_copy_column(self):
        name, source = self.render(sound, self.fixture())
        self.assertEqual(name, 'RuntimeBalanceBlindingTemplateOrdinarySoundness')
        self.assertIn('checked_native 200692', source)
        self.assertIn('RuntimeBalanceBlindingTemplateOrdinaryTrace', source)
        self.assertNotIn('RuntimeTransferEpk', source)

    def test_completion_derives_endpoint_from_rows_on_one_assignment(self):
        _, source = self.render(complete, self.fixture())
        header = source.split('theorem actual_native_scalar_complete', 1)[1].split(' :\n    let ', 1)[0]
        self.assertNotIn('Satisfies', header)
        self.assertNotIn('endpoint', header)
        self.assertIn('actual_native_prefix', source)
        self.assertIn('actual_native_complete_prior', source)

    def test_completion_rejects_changed_singleton_bit_lc(self):
        fixture = self.fixture()
        fixture['checked']['chunks'][0]['expressions'][(0, 2)] = ((22235, 1),)
        with self.assertRaisesRegex(RelationError, 'exact250'):
            self.render(complete, fixture)

    def test_missing_or_reordered_pages_refuse(self):
        for renderer in (sound, complete):
            for mutation in ('missing', 'reordered'):
                fixture = self.fixture()
                if mutation == 'missing':
                    fixture['checked']['chunks'].pop()
                else:
                    fixture['checked']['chunks'].reverse()
                with self.subTest(renderer=renderer.__name__, mutation=mutation):
                    with self.assertRaisesRegex(RelationError, 'eight-page126'):
                        self.render(renderer, fixture)

    def test_canonical_construction_uses_actual_private_column(self):
        _, source = self.render(preserve, self.fixture())
        self.assertIn('(meaning : rho 9 = (n : F))', source)
        self.assertIn('RuntimeBalanceBlindingCanonical.originalRows', source)
        for changed in ('value', 'bit_start'):
            fixture = self.fixture()
            fixture['canonical'][changed] += 1
            with self.subTest(changed=changed), self.assertRaisesRegex(RelationError, 'allocation'):
                self.render(preserve, fixture)

    def test_canonical_preservation_rejects_changed_folded_frame(self):
        fixture = copy.deepcopy(self.fixture())
        fixture['bounds']['frames'][0]['before']['low'] += 1
        with self.assertRaisesRegex(RelationError, 'folded allocation frame'):
            self.render(preserve, fixture)

    def test_canonical_pages_use_own_reflection_and_actual_bits(self):
        for renderer in (ingress, canonical_sound):
            modules = self.render(renderer, self.fixture(), page=1)
            self.assertEqual(len(modules), 1)
            self.assertIn('22232+', modules[0][1])
            self.assertNotIn('RuntimeTransferEpk', modules[0][1])
        modules = self.render(canonical_sound, self.fixture(), page=0)
        self.assertIn('TransferBalanceBlindingCanonicalReflection', modules[0][1])
        self.assertEqual(len(modules), 2)


if __name__ == '__main__':
    unittest.main()
