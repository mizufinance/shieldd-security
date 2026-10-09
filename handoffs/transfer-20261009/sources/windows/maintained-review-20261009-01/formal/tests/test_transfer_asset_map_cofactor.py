"""Independent complete affine doubles and exact bounded source-path checks."""
import copy
import io
import re
import unittest

from circuits import transfer_asset_map as maps, transfer_asset_map_cofactor as cofactor
from circuits import transfer_relation as relation
from tests.test_transfer_asset_map import fixture
from tests.test_asset_asserted_squares import defer_captured


class CofactorJoinTests(unittest.TestCase):
    def test_original_three_doubles_and_corrupted_output_rows(self):
        data, caller, stream, _, builder = fixture(17)
        p = relation.MODULUS
        for data, caller, raw, builder in (
                (data, caller, stream.getvalue(), builder),
                defer_captured(data, caller, stream.getvalue(), builder)):
            extracted = maps.extract(data, io.BytesIO(raw), caller)
            certificates = maps.certificates(data, extracted, caller)
            checked = certificates['checked']
            evaluate = lambda lc, rho: sum(rho[c] * n for c, n in lc) % p
            point = tuple(evaluate(lc, builder.rho) for lc in checked['points'][0])
            for stage in range(3):
                x, y = point
                delta = maps.D * x * x * y * y % p
                self.assertNotEqual((1 + delta) % p, 0)
                self.assertNotEqual((1 - delta) % p, 0)
                point = (2 * x * y * pow(1 + delta, -1, p) % p,
                         (x*x + y*y) * pow(1 - delta, -1, p) % p)
                actual = tuple(evaluate(lc, builder.rho) for lc in checked['points'][stage + 1])
                self.assertEqual(actual, point)
                self.assertEqual((point[1]**2 - point[0]**2 - 1 -
                                  maps.D * point[0]**2 * point[1]**2) % p, 0)
                plan = cofactor._plan(checked, stage)
                # The two cross products retain their separate allocated LCs.
                self.assertNotEqual(plan['selected']['crossLeft'][4], plan['selected']['crossRight'][4])
                corrupted = dict(builder.rho)
                column = checked['points'][stage + 1][0][0][0]
                corrupted[column] = (corrupted[column] + 1) % p
                self.assertTrue(any(evaluate(a, corrupted)**2 % p != evaluate(b, corrupted)
                                    for a, b in certificates['raw'].values()))
            modules = cofactor.generate_doubles(data, extracted, caller)
            self.assertEqual(len(modules), 3)
            for name, source in modules.items():
                exports = re.findall(r'#check @([A-Za-z0-9_]+)', source)
                self.assertEqual(exports, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
                self.assertLessEqual(len(exports), 11)
                self.assertIn('Group.shared_inverse_double_sound', source)
                self.assertNotIn('(outputValue :', source)
                self.assertNotIn('(inverseRow :', source)
                self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')
            name, source = cofactor.generate(data, extracted, caller)
            self.assertEqual(name, 'RuntimeTransferAssetMapCofactor')
            self.assertEqual(source.count('#check @'), 5)
            self.assertIn('Group.cofactor_image_annihilated', source)
            self.assertNotIn('(valid :', source)
            self.assertNotIn('(first :', source)
            self.assertIn('(standardOrder : ∀ point : J,', source)
            _, native_source = cofactor.generate_native(data, extracted, caller)
            self.assertEqual(native_source.count('#check @'), 1)
            self.assertIn('GroupNativeCofactor.nativeEight', native_source)
            self.assertIn('unfold GroupNativeCofactor.nativeEight\n    dsimp only\n    rw [nativeFirst,nativeSecond,nativeThird]',native_source)
            self.assertNotIn('(standardOrder :', native_source)
            self.assertNotIn('(nativeOutput :', native_source)
            altered = copy.deepcopy(extracted)
            altered['selected_rows'].pop()
            with self.assertRaises(relation.RelationError):
                cofactor.generate(data, altered, caller)


if __name__ == '__main__':
    unittest.main()
