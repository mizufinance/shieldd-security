"""Observed paging resource successor leaves all test/native source semantics fixed."""
from pathlib import Path
import hashlib,json,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
OLD=P/'transfer-v2-five-controls-execution-04'
NEW=P/'transfer-v2-five-controls-execution-05'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
class ControlsResidentSuccessorTests(unittest.TestCase):
    def test_exact_fourteen_test_commands_and_safe_resource_delta(self):
        a=json.loads((OLD/'manifest.json').read_bytes());b=json.loads((NEW/'manifest.json').read_bytes())
        for key in ('registry','setup_output','pin','source_packet','source_packet_inputs_sha256','source_child','source_parent','setup_binary_sha256','native_setup_sources','lock_sha256','setup_budgets','setup_success_inputs','setup_publication_sha256','header_compatibility','cpp_version_inputs'):
            self.assertEqual(a[key],b[key])
        self.assertEqual(b['budgets'],dict(a['budgets'],resident_MiB=3072,host_physical_admit_KiB=5767168,host_commit_admit_KiB=4718592))
        for old,new in zip(a['jobs'],b['jobs'],strict=True):
            self.assertEqual({k:v for k,v in old.items()if k!='output'},{k:v for k,v in new.items()if k!='output'})
            name=f"test-{new['index']:02}.sh"
            expected=(OLD/name).read_text().replace(OLD.name,NEW.name).replace(old['output'],new['output'])
            expected=expected.replace("printf '805306368\\n' > \"$cg/memory.max\"","printf '3221225472\\n' > \"$cg/memory.max\"",1)
            expected=expected.replace('[ "$host_available" -ge 3145728 ] && [[ "$commit_free" =~ ^[0-9]+$ ]] && [ "$commit_free" -ge 1572864 ]','[ "$host_available" -ge 5767168 ] && [[ "$commit_free" =~ ^[0-9]+$ ]] && [ "$commit_free" -ge 4718592 ]',1)
            self.assertEqual((NEW/name).read_text(),expected)
            shell=(NEW/name).read_text()
            self.assertIn('"$host_available" -lt 1572864',shell)
            self.assertIn('"$commit_free" -lt 524288',shell)
            self.assertIn("printf '8589934592\\n'",shell)
            self.assertIn('fallocate -l 6442450944',shell)
            self.assertIn(str(new['seconds'])+' /usr/bin/time',shell)
            wrapper=(NEW/f"test-{new['index']:02}.ps1").read_text()
            self.assertLess(wrapper.index('3GiB native test admission before WSL'),wrapper.index('Start-Process'))
        self.assertEqual(len(b['jobs']),14)

    def test_exact_stopped_receipts_and_no_semantic_credit(self):
        cfg=json.loads((NEW/'manifest.json').read_bytes())
        for raw,digest in cfg['resource_failure_inputs'].items():self.assertEqual(sha(raw),digest)
        self.assertIn('no semantic test credit',cfg['resource_scope'])
        self.assertIn('580514',cfg['resource_scope'])
        for path in NEW.glob('*.py'):compile(path.read_bytes(),str(path),'exec')
        self.assertEqual(len(list(NEW.glob('*.sh'))),30)
        for path in NEW.glob('*.sh'):self.assertNotIn(b'\r',path.read_bytes())
        for name,digest in json.loads((NEW/'inputs.json').read_bytes()).items():self.assertEqual(sha(NEW/name),digest)
        recipe=json.loads((P/'transfer-v2-five-controls-execution-root-recipe-05.json').read_bytes())
        self.assertEqual(recipe['new_setup_jobs'],0)
        self.assertEqual(sha(P/recipe['coordinator']),recipe['coordinator_sha256'])
        self.assertEqual(sha(NEW/'inputs.json'),recipe['inputs_sha256'])
        self.assertIn('-lt 5767168',(P/recipe['coordinator']).read_text())
