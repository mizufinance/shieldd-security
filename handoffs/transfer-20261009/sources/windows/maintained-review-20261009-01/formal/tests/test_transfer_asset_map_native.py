"""Independent native sqrt/byte parity checks on bounded source-row fixtures."""
import copy
import io
import re
import unittest

from circuits import transfer_asset_map as maps, transfer_asset_map_native as native
from circuits import transfer_relation as relation
from tests.test_transfer_asset_map import fixture, square_root
from tests.test_asset_asserted_squares import defer_captured


class NativeRootTests(unittest.TestCase):
    def test_canonical_native_flip_and_strict_actual_rows(self):
        branches = set()
        p = relation.MODULUS
        for u in (0, 2, 17):
            data, caller, stream, _, builder = fixture(u)
            for data, caller, raw, builder in (
                    (data, caller, stream.getvalue(), builder),
                    defer_captured(data, caller, stream.getvalue(), builder)):
                extracted = maps.extract(data, io.BytesIO(raw), caller)
                checked = maps.inspect_metadata(data, caller)
                evaluate = lambda lc: sum(builder.rho[c] * n for c, n in lc) % p
                # Reproduce primitive map.rs selection using independent field
                # arithmetic and Tonelli-Shanks, without reading its witnesses.
                tv = 5 * u * u % p
                x1 = -maps.C1 * pow(1 + tv, -1, p) % p
                gx1 = ((x1 + maps.C1) * x1 + maps.C2) * x1 % p
                root = square_root(gx1)
                option = root is not None
                branches.add(option)
                x = x1 if option else (-x1 - maps.C1) % p
                y = root if option else square_root(tv * gx1)
                self.assertIsNotNone(y)
                if (y & 1) ^ int(option):
                    y = -y % p
                self.assertEqual(evaluate(checked['values']['x']), x)
                self.assertEqual(evaluate(checked['values']['y']), y)
                self.assertEqual(y & 1, int(option))
                if y:
                    self.assertNotEqual((-y % p) & 1, int(option))
                # A flipped nonzero root still passes the square equation;
                # the original canonical parity row excludes it.
                self.assertEqual(y * y % p, (-y % p)**2 % p)
                name, source = native.generate(data, extracted, caller)
                self.assertEqual(name, 'RuntimeTransferAssetMapNativeRoot')
                checks = re.findall(r'#check @([A-Za-z0-9_]+)', source)
                self.assertEqual(len(checks), 6)
                self.assertEqual(checks, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
                self.assertIn('RuntimeTransferAssetMapEncoding.actual_parity', source)
                self.assertIn('ElligatorNative.codec_root_unique', source)
                self.assertIn('(nativeSquare : nativeY * nativeY =', source)
                self.assertIn('(nativeParity : codec.decode nativeY % 2', source)
                self.assertNotIn('(rootEqual :', source)
                self.assertNotIn('(imageEqual :', source)
                self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')
                bad = copy.deepcopy(extracted)
                bad['selected_rows'].pop()
                with self.assertRaises(relation.RelationError):
                    native.generate(data, bad, caller)
        self.assertEqual(branches, {False, True})


if __name__ == '__main__':
    unittest.main()
