"""Owned generator composition source and exact dependency recipe checks only."""
from pathlib import Path
import hashlib,json,re,unittest

R=Path('C:/src/shieldd-formal')
P=R/'.work/diagnostics/transfer-implementation-20261002'

class NativeAssetGeneratorSourceTests(unittest.TestCase):
    def test_owned_order_same_object_and_explicit_contracts(self):
        body=(R/'circuits/ShielddSecurity/NativeAssetGeneratorSource.lean').read_text()
        native=Path('C:/src/shieldd-pr160-844389ee/crates/core/asset/src/asset/id.rs').read_text()
        self.assertIn('map::to_subgroup(&shieldd_sdk_crypto::poseidon::hash(',native)
        self.assertIn('shieldd_sdk_crypto::domains::ASSET_GENERATOR,',native)
        self.assertIn('&[self.0],',native)
        self.assertIn('NativeAssetHashParameters.asset_source_object',body)
        self.assertIn('NativeAssetMap.toSubgroup fq api ops points\n    (hashObject',body)
        self.assertIn('NativeAssetMap.to_subgroup_coordinates',body)
        self.assertIn('ShielddNativeSdk.native_point_read',body)
        self.assertNotIn('HashMapABI',body)
        self.assertNotIn('mapMeaning',body)
        self.assertNotRegex(body,r'\b(sorry|admit|native_decide|axiom)\b')
        checks=re.findall(r'^#check @([\w.]+)',body,re.M)
        self.assertEqual(checks,['hash_object','coordinates','native_point'])
        self.assertEqual(checks,re.findall(r'^#print axioms ([\w.]+)',body,re.M))
        self.assertEqual(body.count('set_option pp.all true in'),3)

    def test_frozen_source_and_actual_dependency_receipts(self):
        packet=P/'native-asset-generator-source-03'
        summary=json.loads((packet/'summary.json').read_bytes())
        self.assertEqual(summary['modules'],{'NativeAssetGeneratorSource':3})
        for relative,digest in summary['files'].items():
            self.assertEqual(hashlib.sha256((packet/relative).read_bytes()).hexdigest(),digest)
        for raw,digest in summary['inputs'].items():
            self.assertEqual(hashlib.sha256(Path(raw).read_bytes()).hexdigest(),digest)
        addition='include imaginary nonSquare imaginarySquare kNonzero denominator edwards odd fiveNonzero fiveEuler in\n'
        old=(P/'native-asset-generator-source-02/NativeAssetGeneratorSource.lean').read_text()
        new=(packet/'NativeAssetGeneratorSource.lean').read_text()
        comment=old[old.index('/-- The variable-loop base'):old.index('theorem native_point')]
        self.assertTrue(comment.endswith(addition))
        self.assertEqual(new,old.replace(comment,addition+comment.removesuffix(addition),1))
        self.assertNotRegex(new,r'-/\s*include\s')
        self.assertEqual(new.count(addition),2)
        driver=P/'prepare-native-asset-generator-source-03.py'
        compile(driver.read_bytes(),str(driver),'exec')
        body=driver.read_text()
        self.assertIn("leaf('narrow-native-asset-map-05-kernel','NativeAssetMap',9)",body)
        self.assertIn("leaf('narrow-native-asset-parameters-02-kernel','NativeAssetHashParameters',6)",body)
        self.assertIn('prepare-exact-source-kernel-01.py',body)
        self.assertNotIn('relation.jsonl',body)
        self.assertIn("failed=P/'narrow-native-asset-generator-source-02-kernel/NativeAssetGeneratorSource'",body)
        self.assertIn('Only documentation/include ordering repair allowed',body)
        recipe=json.loads((P/'native-asset-generator-source-root-recipe-04.json').read_bytes())
        self.assertEqual(hashlib.sha256(driver.read_bytes()).hexdigest(),recipe['driver_sha256'])
        guard=P/'prepare-native-asset-generator-source-04.ps1'
        self.assertEqual(hashlib.sha256(guard.read_bytes()).hexdigest(),recipe['guard_sha256'])
        self.assertIn(recipe['driver_sha256'],guard.read_text())
        self.assertIn('PrivateMemorySize64 -gt 134217728',guard.read_text())
        self.assertFalse(recipe['qualification'])
        self.assertIn('native-asset-generator-source-prep-04',guard.read_text())
        self.assertNotIn('native-asset-generator-source-prep-02',guard.read_text())
        previous=(P/'prepare-native-asset-generator-source-03.ps1').read_bytes()
        self.assertEqual(guard.read_bytes(),previous.replace(
            b'native-asset-generator-source-prep-02',b'native-asset-generator-source-prep-04'))
        self.assertEqual(recipe['root_order'],[
            'prepare-native-asset-generator-source-04.ps1','narrow-native-asset-generator-source-03-kernel.ps1'])
