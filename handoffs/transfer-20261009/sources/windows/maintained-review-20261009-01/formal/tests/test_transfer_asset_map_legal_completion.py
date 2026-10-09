"""Local map-input admission/constructor; actual assetHash remains separate."""
import re
import unittest
from circuits import transfer_asset_map_legal_completion as legal
from tests.test_transfer_asset_map_inverse_frame import fixture


class LegalMapCompletionTests(unittest.TestCase):
    def test_exact_same_parent_and_native_success_discharge_original_inverse(self):
        data, extracted, parent, inverse_extracted, caller, _ = fixture()
        result = legal.plan(data, extracted, parent, inverse_extracted, caller)
        self.assertEqual(len(result['map']['recipe']['raw']), 870)
        self.assertEqual(len(result['inverse']['raw']), 3)
        name, source = legal.generate(data, extracted, parent, inverse_extracted, caller)
        self.assertEqual(name, 'RuntimeTransferAssetMapLegalCompletion')
        checks = re.findall(r'#check @([A-Za-z0-9_]+)', source)
        self.assertEqual(len(checks), 5)
        self.assertEqual(checks, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
        self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')
        statement = source[source.index('theorem complete_rows'):].split(':= by', 1)[0]
        for forbidden in ('(satisfied', '(legal', '(nonidentity', '(nativePoint', '(nativeImage'):
            self.assertNotIn(forbidden, statement)
        self.assertIn('NativeTransferAdmission.balanceNative', statement)
        self.assertIn('balance_success_nonidentity', source)
        self.assertIn('model.covers', source)
        self.assertIn('subgroup_nonidentity_x', source)
        self.assertIn('NativeSource.native_program', source)
        self.assertIn('InverseCompletion.complete_rows', source)
        self.assertIn('InverseFrame.map_rows_complete', source)
        self.assertIn('Actual domain26 asset/hash input', source)


if __name__ == '__main__':
    unittest.main()
