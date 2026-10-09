import hashlib,json,unittest
from pathlib import Path

P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')

class RemainingNativeSwapQueueTests(unittest.TestCase):
    def test_all_exact_fresh_parent_command_resource_and_cleanup_associations(self):
        recipe=json.loads((P/'remaining-native-capture-root-recipes-03.json').read_bytes())
        self.assertEqual(len(recipe['jobs']),24)
        for name in recipe['jobs']:
            shell=(P/(name+'.sh')).read_bytes();text=shell.decode();ps=(P/(name+'.ps1')).read_text()
            cleanup=(P/('cleanup-'+name+'.sh')).read_bytes()
            self.assertNotIn(b'\r',shell);self.assertNotIn(b'\r',cleanup)
            self.assertIn(name+'.sh',ps);self.assertIn('cleanup-'+name+'.sh',ps)
            self.assertIn('/'+name,text);self.assertIn('/'+name,cleanup.decode())
            self.assertIn('epk-all-build-guard-14/frozen-binary.sha256',text)
            self.assertIn('native_sdk_receipt_preflight.py',text)
            scope,phase,version=name.removeprefix('remaining-').rsplit('-',2)
            if phase in ('first','repeat'):
                self.assertEqual(version,'03')
                self.assertIn('fallocate -l 4294967296 "$task_swap"',text)
                self.assertIn('swapon --priority 100 "$task_swap"',text)
                self.assertIn("printf '5368709120\\n' > \"$cg/memory.swap.max\"",text)
                self.assertIn("printf '2147483648\\n' > \"$cg/memory.max\"",text)
                self.assertIn('-ge 4718592',text);self.assertIn('-ge 3670016',text)
                self.assertIn('2400 /usr/bin/time',text)
                self.assertIn('transfer-'+name+'.swap',cleanup.decode())
                if scope=='roles':self.assertIn(' roles-spool ',text)
                else:self.assertIn(' remaining-pages-spool '+scope+' ',text)
            else:
                self.assertIn('remaining-'+scope+'-first-03/capture',text)
                self.assertIn('remaining-'+scope+'-repeat-03/capture',text)
                self.assertNotIn('remaining-'+scope+'-repeat-02',text)
                self.assertIn("printf '805306368\\n' > \"$cg/memory.max\"",text)
                if scope=='roles':
                    self.assertEqual(version,'05');self.assertIn(' qualify-spools ',text)
                    self.assertIn("-contains 'repeated_observations_equal'",ps)
                else:
                    self.assertEqual(version,'04')
                    self.assertIn('remaining_page_reader_aliases.py '+scope+' ',text)
                    self.assertIn('remaining_page_reader_aliases.py audit',text)
            self.assertIn('-lt 1572864',text);self.assertIn('-lt 524288',text)
        for raw,digest in recipe['files'].items():
            self.assertEqual(hashlib.sha256(Path(raw).read_bytes()).hexdigest(),digest)
