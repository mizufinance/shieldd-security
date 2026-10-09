"""Independent native root choices normalize to the same owned map point."""
from pathlib import Path
import re
import unittest
from circuits.transfer_relation import MODULUS as P
from tests.test_transfer_asset_map import square_root


class RootInteropTests(unittest.TestCase):
    def test_opposite_native_roots_both_branches_and_exception(self):
        k = -40964 % P
        c1 = 40962 * pow(k, -1, P) % P
        c2 = pow(k, -2, P)
        branches = set()
        distinct = 0
        for u in (0, 2, 17):
            x1 = -c1 * pow(1+5*u*u, -1, P) % P
            first = ((x1+c1)*x1+c2)*x1 % P
            self.assertNotEqual(first, 0)
            chosen = square_root(first) is not None
            branches.add(chosen)
            selected = first if chosen else 5*u*u*first % P
            root = square_root(selected)
            self.assertIsNotNone(root)
            opposite = -root % P
            self.assertEqual(root*root % P, opposite*opposite % P)
            normalized = lambda value: value if value % 2 == int(chosen) else -value % P
            self.assertEqual(normalized(root), normalized(opposite))
            self.assertEqual(normalized(root) % 2, int(chosen))
            distinct += root != opposite
            if u == 0:
                self.assertFalse(chosen)
                self.assertEqual((root, opposite), (0, 0))
        self.assertEqual(branches, {False, True})
        self.assertGreater(distinct, 0)

    def test_helper_contract_has_separate_functional_abis_and_audits(self):
        source = (Path(__file__).resolve().parents[1]/'circuits/ShielddSecurity/ElligatorNativeRootInterop.lean').read_text()
        exports = re.findall(r'#check @([A-Za-z0-9_]+)', source)
        self.assertEqual(len(exports), 4)
        self.assertEqual(exports, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
        self.assertEqual(source.count('set_option pp.all true in'), 4)
        self.assertIn('(left.complete value).trans (right.complete value).symm', source)
        self.assertIn('ElligatorNative.codec_root_unique codec', source)
        self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')
        for declaration in re.findall(r'theorem .*?:= by', source, re.S):
            self.assertNotIn('(rawRootEqual', declaration)
            self.assertNotIn('(outputEqual', declaration)

    def test_actual_renderer_derives_first_cubic_and_transports_api(self):
        from circuits import transfer_asset_map_root_interop as interop
        from circuits import transfer_asset_map as maps
        from tests.test_transfer_asset_map_canonical_sequence import deferred_sequence_fixture
        data, caller, stream, _ = deferred_sequence_fixture()
        extracted = maps.extract(data, stream, caller)
        name, source = interop.generate(data, extracted, caller)
        self.assertEqual(name, 'RuntimeTransferAssetMapRootInterop')
        exports = re.findall(r'#check @([A-Za-z0-9_]+)', source)
        self.assertEqual(len(exports), 3)
        self.assertEqual(exports, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
        self.assertIn('RuntimeTransferAssetMapFirstCubicConstruction.native_first_nonzero cardinality rho', source)
        self.assertIn('RuntimeTransferAssetMapNativeSource.actual_native_program', source)
        tail = source[source.index('theorem actual_other_api'):].split(':=')[0]
        for forbidden in ('(firstNonzero', '(rootEqual', '(satisfied', '(nativeResult'):
            self.assertNotIn(forbidden, tail)


if __name__ == '__main__':
    unittest.main()
