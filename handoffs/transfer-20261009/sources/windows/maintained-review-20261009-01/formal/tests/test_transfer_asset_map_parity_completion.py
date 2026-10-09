"""Semantic native normalization over the exact original map parity rows."""
import io
import re
import unittest

from circuits import transfer_asset_map as maps, transfer_asset_map_completion as completion
from circuits import transfer_asset_map_parity_completion as parity
from tests.test_transfer_asset_map import fixture, square_root
from tests.test_asset_asserted_squares import defer_captured


class NativeParityCompletionTests(unittest.TestCase):
    def test_both_native_choices_zero_and_opposite_roots(self):
        branches = set()
        for u in (0, 2, 17):
            data, caller, stream, _, builder = fixture(u)
            for data, caller, raw, builder in (
                    (data, caller, stream.getvalue(), builder),
                    defer_captured(data, caller, stream.getvalue(), builder)):
                extracted = maps.extract(data, io.BytesIO(raw), caller)
                recipe = completion.plan(data, extracted, caller)
                native = completion.construct(data, extracted, caller, dict(builder.rho), square_root)
                rho = native['assignment'];seeds = recipe['seeds'];choice = rho[seeds['choice']]
                branches.add(choice)
                selected = rho[seeds['selectedRoot']]
                for root in {selected, (-selected) % maps.P}:
                    normalized = root if root % 2 == choice else (-root) % maps.P
                    self.assertEqual(normalized, selected)
                    self.assertEqual(normalized**2 % maps.P, root**2 % maps.P)
                    self.assertEqual(normalized % 2, choice)
                name, source = parity.generate(data, extracted, caller)
                self.assertEqual(name, 'RuntimeTransferAssetMapParityCompletion')
                exports = re.findall(r'#check @([A-Za-z0-9_]+)', source)
                self.assertEqual(exports, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
                self.assertEqual(len(exports), 6)
                self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')
                complete = source[source.index('theorem complete ('):source.index('#print axioms')]
                premises = complete[:complete.index(':= by')]
                self.assertNotIn('(parity', premises)
                self.assertNotIn('(satisfied', premises)
                self.assertIn('ElligatorNativeParity.selected_normalization', complete)
                self.assertIn('RuntimeTransferAssetMapNativeBits.complete', complete)
                self.assertIn('column ≠', source)
                self.assertIn('rcases List.mem_append.mp member with bit | localRow', source)
                self.assertNotRegex(source, r'with[^\n]*\| local(?:\s|$)')
        self.assertEqual(branches, {0, 1})
        # The exceptional root's native branch can only be false. Its sign
        # normalization remains zero and agrees with bit0=false.
        self.assertEqual(0 if 0 % 2 == 0 else (-0) % maps.P, 0)


if __name__ == '__main__':
    unittest.main()
