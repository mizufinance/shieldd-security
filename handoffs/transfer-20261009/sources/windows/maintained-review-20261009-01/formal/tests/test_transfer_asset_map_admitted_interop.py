"""Existing actual ownership/admission and separate functional sqrt interfaces."""
import re
import unittest
from circuits import transfer_asset_map_admitted_interop as interop


class AdmittedInteropTests(unittest.TestCase):
    def test_exact_imported_source_and_hash_input_join(self):
        name, source = interop.generate()
        self.assertEqual(name, 'RuntimeTransferCompleteAssetConeInterop')
        self.assertIn('RuntimeTransferAssetMapHashJoin.map_input_value rho one linked', source)
        self.assertIn('RuntimeTransferAssetMapRootInterop.source_first_nonzero cardinality', source)
        self.assertIn('ElligatorNativeRootInterop.generator_agreement codec circuitApi sdkApi', source)
        self.assertIn('RuntimeTransferCompleteAssetCone.complete_rows', source)
        self.assertNotIn('def rawRows', source)

    def test_native_domain_remains_independent_and_copy_is_constructed(self):
        _, source = interop.generate()
        declaration = source[source.index('theorem complete_rows'):].split(':=')[0]
        self.assertIn('NativeAssetAdmission.proofDataNative fetch (rho 6) = .ok proof', declaration)
        self.assertIn('nativeAssetGenerator codec sdkApi', declaration)
        self.assertIn('completeAssignment codec circuitApi rho', declaration)
        for forbidden in ('(firstNonzero', '(rootEqual', '(nonidentity', '(satisfied', '(linked'):
            self.assertNotIn(forbidden, declaration)
        self.assertIn('initialCopy.trans initialOne.symm', source)
        self.assertIn('agreeing.trans accepted', source)

    def test_full_signatures_finite_budget_no_new_axioms(self):
        _, source = interop.generate()
        checks = re.findall(r'#check @([A-Za-z0-9_]+)', source)
        self.assertEqual(len(checks), 3)
        self.assertEqual(checks, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
        self.assertEqual(source.count('set_option pp.all true in'), 3)
        self.assertIn('set_option maxHeartbeats 400000', source)
        self.assertIn('set_option maxRecDepth 4096', source)
        self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')


if __name__ == '__main__':
    unittest.main()
