"""No renderer/replay: exact audited same-batch parent resolution and source delta."""
from pathlib import Path
import hashlib,json,runpy,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
class OwnedSeedSiblingRecipeTests(unittest.TestCase):
    def test_unchanged_math_and_strict_actual_parent_scope(self):
        old=P/'balance-owned-asset-seed-reuse-source-03';new=P/'balance-owned-asset-seed-reuse-source-04'
        a=json.loads((old/'manifest.json').read_bytes());b=json.loads((new/'manifest.json').read_bytes())
        for rel,digest in a['files'].items():
            if rel!='driver.py':self.assertEqual((old/rel).read_bytes(),(new/rel).read_bytes())
        for raw,digest in b['inputs'].items():self.assertEqual(hashlib.sha256(Path(raw).read_bytes()).hexdigest(),digest)
        expected=(old/'driver.py').read_text().replace('prepare-native-asset-generator-source-03.py','owned-asset-seed-actual-parents-01.py').replace('balance-owned-asset-seed-reuse-actual-source-03','balance-owned-asset-seed-reuse-actual-source-04')
        self.assertEqual((new/'driver.py').read_text(),expected)
        helper=(P/'owned-asset-seed-actual-parents-01.py').read_text()
        self.assertIn('left is None and right is None and batch.name==allowed_batch and imported in allowed',helper)
        self.assertIn('range(8,13)',helper)
        self.assertIn('sibling,_=leaf(allowed_batch,imported,allowed[imported])',helper)
        self.assertIn('exact imported receipt mismatch parent=',helper)
        for path in(new/'driver.py',P/'owned-asset-seed-actual-parents-01.py',P/'prepare-owned-asset-seed-kernel-04.py'):
            compile(path.read_bytes(),str(path),'exec')

    def test_five_actual_successful_siblings_are_targets_not_external_snapshot_entries(self):
        # Small receipt schema fixture only. Full current-object/transitive
        # parent acceptance remains in the root512MiB/600s generation driver.
        batch=P/'narrow-t4-asset-hash-actual-04-kernel'
        self.assertTrue((batch/'complete.txt').is_file())
        manifest=json.loads((batch/'manifest.json').read_bytes())
        before=json.loads((batch/'dependencies-before.json').read_bytes())
        after=json.loads((batch/'dependencies-after.json').read_bytes())
        for i in range(8,13):
            name=f'RuntimeTransferActualAssetHashCompletionChunk{i}'
            leaf=batch/name;source=leaf/'source.lean'
            self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(),manifest[name])
            self.assertEqual((leaf/'exit.txt').read_bytes(),b'0\r\n')
            audit=json.loads((leaf/'audit.json').read_bytes())
            self.assertEqual(audit['source_sha256'],manifest[name])
            self.assertEqual(len(audit['names']),10)
            for snapshot in(before,after):
                self.assertFalse(any(Path(row['path']).name in(name+'.lean',name+'.olean')for row in snapshot))
