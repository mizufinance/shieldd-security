"""Frozen root-only producer/kernel wiring; does not execute either driver."""
from pathlib import Path
import hashlib,json,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')

class BalanceOwnedAssetSeedRecipeTests(unittest.TestCase):
    def test_frozen_real_drivers_and_no_ordinary_scan(self):
        packet=P/'balance-owned-asset-seed-reuse-source-03'
        manifest=json.loads((packet/'manifest.json').read_bytes())
        for name,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((packet/name).read_bytes()).hexdigest(),digest)
        for path,digest in manifest['inputs'].items():
            self.assertEqual(hashlib.sha256(Path(path).read_bytes()).hexdigest(),digest)
        driver=(packet/'driver.py').read_text()
        compile(driver,str(packet/'driver.py'),'exec')
        self.assertIn("('narrow-native-asset-generator-source-03-kernel','NativeAssetGeneratorSource',3)",driver)
        self.assertNotIn('native-asset-generator-source-02',driver)
        old=P/'balance-owned-asset-seed-reuse-source-02'
        for name in manifest['files']:
            if name!='driver.py':self.assertEqual((packet/name).read_bytes(),(old/name).read_bytes())
        self.assertIn("('narrow-t4-asset-hash-actual-04-kernel','RuntimeTransferActualAssetHashCompletion',6)",driver)
        self.assertIn('reuse.generate_owned',driver)
        self.assertIn("'actual_parent_flags_unchanged']is not True",driver)
        self.assertIn("Path(p).name=='relation.jsonl'",driver)
        self.assertNotIn("spec['ordinary']",driver)
        self.assertIn("str(joint).replace('\\\\','/')",driver)

    def test_named_kernel_route_is_finite_and_exit_before_audit(self):
        recipe=json.loads((P/'balance-owned-asset-seed-reuse-root-recipe-04.json').read_bytes())
        self.assertEqual(recipe['modules'],{'RuntimeBalanceOwnedAssetSeedReuse':8})
        self.assertEqual(recipe['manifest_sha256'],hashlib.sha256((P/recipe['source_packet']/'manifest.json').read_bytes()).hexdigest())
        self.assertEqual(recipe['guard_sha256'],hashlib.sha256((P/recipe['root_generation_guard']).read_bytes()).hexdigest())
        self.assertEqual(recipe['metadata_guard_sha256'],hashlib.sha256((P/'prepare-owned-asset-seed-kernel-03.ps1').read_bytes()).hexdigest())
        driver=P/'prepare-owned-asset-seed-kernel-03.py'
        self.assertEqual(recipe['metadata_driver_sha256'],hashlib.sha256(driver.read_bytes()).hexdigest())
        body=driver.read_text();compile(body,str(driver),'exec')
        self.assertIn("check+'\\n'+command",body)
        self.assertIn('Start-Sleep -Milliseconds 400',body)
        self.assertIn("'.TotalSeconds -ge 240'in wrapper",body)
        guard=(P/'prepare-owned-asset-seed-kernel-03.ps1').read_text()
        self.assertIn('owned-asset-seed-kernel-prep-03',guard)
        self.assertNotIn('owned-asset-seed-kernel-prep-02',guard)
        self.assertIn('PrivateMemorySize64 -gt 134217728',guard)
        self.assertIn('.TotalSeconds -ge 120',guard)
        self.assertIn(recipe['metadata_driver_sha256'],guard)
        self.assertFalse(recipe['qualification'])
