"""Construct exact owned map rows from arbitrary auxiliary values/native input."""
import io
import re
import unittest

from circuits import transfer_asset_map as maps, transfer_asset_map_completion as completion
from circuits import transfer_asset_map_native_constructor as native_constructor
from circuits import transfer_relation as relation
from tests.test_transfer_asset_map import fixture, square_root
from tests.test_asset_asserted_squares import defer_captured


class MapCompletionTests(unittest.TestCase):
    def test_construct_all_original_rows_from_arbitrary_owned_columns(self):
        branches = set()
        p = relation.MODULUS
        for u in (0, 2, 17):
            data, caller, stream, _, builder = fixture(u)
            for data, caller, raw, builder in (
                    (data, caller, stream.getvalue(), builder),
                    defer_captured(data, caller, stream.getvalue(), builder)):
                extracted = maps.extract(data, io.BytesIO(raw), caller)
                recipe = completion.plan(data, extracted, caller)
                base = dict(builder.rho)
                base.update({column: (column * 19 + 37) % p for column in recipe['owned_writes']})
                base.update({1: 83, 2: 97, 32767: 113})
                built = completion.construct(data, extracted, caller, base, square_root)
                rho = built['assignment']
                branches.add(rho[recipe['seeds']['choice']])
                self.assertFalse(built['proof'])
                self.assertEqual(len(recipe['seeds']), 264)
                self.assertEqual(len(recipe['raw']), len(recipe['material_rows']) + len(recipe['assertion_rows']) + 1)
                self.assertEqual([rho[c] for c in (0, 1, 2, 32000, 32767)], [1, 83, 97, 1, 113])
                for c, value in base.items():
                    if c not in recipe['owned_writes']:
                        self.assertEqual(rho[c], value)
                evaluate = lambda lc: sum(rho.get(c, 0) * n for c, n in lc) % p
                self.assertTrue(all(evaluate(a)**2 % p == evaluate(b) for a, b in recipe['raw'].values()))
                # The final cofactor coordinates are derived by construction,
                # never provided to the assignment planner as desired values.
                final = tuple(evaluate(lc) for lc in recipe['checked']['points'][3])
                self.assertEqual(final, built['native_image'])
                self.assertEqual(evaluate(recipe['checked']['values']['u']), u)
                if data.decode().find('asset-map-v2') >= 0:
                    fused = recipe['checked']['asserted_square_nodes']
                    self.assertEqual(len(fused), 2)
                    self.assertTrue(all(node not in [step['source'] for step in recipe['steps']] for node in fused))
        self.assertEqual(branches, {0, 1})

    def test_native_contract_and_kept_constant_fail_closed(self):
        data, caller, stream, _, builder = fixture(17)
        extracted = maps.extract(data, stream, caller)
        with self.assertRaisesRegex(relation.RelationError, 'sqrt/option specification'):
            completion.construct(data, extracted, caller, builder.rho, lambda _: 1)
        base = dict(builder.rho);base[32000] = 0
        with self.assertRaisesRegex(relation.RelationError, 'constant/copy'):
            completion.construct(data, extracted, caller, base, square_root)

    def test_bounded_numeric_row_construction_has_no_assertion_premises(self):
        data, caller, stream, _, _ = fixture(17)
        extracted = maps.extract(data, stream, caller)
        modules = completion.generate_materializations(data, extracted, caller)
        self.assertGreater(len(modules), 30)
        for name, source in modules.items():
            checks = re.findall(r'#check @([A-Za-z0-9_]+)', source)
            self.assertEqual(len(checks), 7)
            self.assertEqual(checks, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
            self.assertIn('CompilerCompletion.run_complete', source)
            self.assertIn('CompilerSignedCompletion.original_rows', source)
            self.assertIn('PoseidonCompletion.run_outside', source)
            self.assertNotIn('(satisfied :', source)
            self.assertNotIn('(legal :', source)
            self.assertNotIn('.squareEqual ', source)
            self.assertNotIn('.equal ', source)
            self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')
        for bound in (True, 0, 17):
            with self.assertRaises(relation.RelationError):
                completion.generate_materializations(data, extracted, caller, chunk_size=bound)

    def test_native_sign_is_constructed_and_parity_is_a_conclusion(self):
        data, caller, stream, _, _ = fixture(17)
        extracted = maps.extract(data, stream, caller)
        name, source = native_constructor.generate(data, extracted, caller)
        self.assertEqual(name, 'RuntimeTransferAssetMapNativeConstruction')
        self.assertEqual(source.count('#check @'), 1)
        self.assertEqual(source.count('#print axioms'), 1)
        self.assertIn('ElligatorNativeParity.selected_normalization', source)
        self.assertIn('ElligatorNativeParity.normalizeRoot', source)
        self.assertNotIn('(nativeParity :', source)
        self.assertNotIn('(selectedRoot :', source)
        self.assertNotIn('(nativeOutput :', source)
        name, bits = completion.generate_native_bits(data, extracted, caller)
        self.assertEqual(name, 'RuntimeTransferAssetMapNativeBits')
        self.assertEqual(bits.count('#check @'), 4)
        self.assertIn('writeBits_range_complete', bits)
        self.assertIn('(codec.bounded nativeValue).trans', bits)
        self.assertNotIn('(meaning :', bits)
        self.assertNotIn('(bound :', bits)
        self.assertNotIn('(satisfied :', bits)
        self.assertNotIn('expectedRows.any', bits)


if __name__ == '__main__':
    unittest.main()
