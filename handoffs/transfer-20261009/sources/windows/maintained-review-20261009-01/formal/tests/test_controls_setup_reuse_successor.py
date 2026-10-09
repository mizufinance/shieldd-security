"""Actual setup receipt adoption and unchanged control semantics, source only."""
from pathlib import Path
import hashlib,json,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
OLD=P/'transfer-v2-five-controls-execution-02'
NEW=P/'transfer-v2-five-controls-execution-03'

class ControlsSetupReuseSuccessorTests(unittest.TestCase):
    def test_actual_setup_receipts_pinned_and_no_new_setup_job(self):
        config=json.loads((NEW/'manifest.json').read_bytes())
        old=json.loads((OLD/'manifest.json').read_bytes())
        for key in ('registry','setup_output','pin','source_packet','source_packet_inputs_sha256',
                    'source_child','source_parent','setup_binary_sha256','native_setup_sources',
                    'lock_sha256','budgets','setup_budgets'):
            self.assertEqual(config[key],old[key])
        self.assertTrue(config['setup_reused'])
        for category in ('setup_success_inputs','test_failure_inputs'):
            for path,digest in config[category].items():
                self.assertEqual(hashlib.sha256(Path(path).read_bytes()).hexdigest(),digest)
        setup=P/config['setup_output']
        for name in ('exit.txt','wrapper-exit.txt'):
            self.assertIn((setup/name).read_bytes(),(b'0\n',b'0\r\n'))
        self.assertEqual((setup/'task-swap-cleanup.txt').read_bytes(),b'removed\n')
        self.assertEqual((setup/'full-source-before.json').read_bytes(),(setup/'full-source-after.json').read_bytes())
        self.assertEqual(hashlib.sha256((setup/'registry-published.json').read_bytes()).hexdigest(),config['setup_publication_sha256'])
        coordinator=(P/'root-five-controls-serial-03.ps1').read_text()
        self.assertIn("$taskGuards=1..14|ForEach-Object",coordinator)
        self.assertNotIn("@('setup06.ps1')",coordinator)
        self.assertIn('setup_success_inputs',coordinator)
        self.assertIn('PhysicalKiB -lt 3145728',coordinator)
        self.assertIn('CommitFreeKiB -lt 1572864',coordinator)
        guard=(NEW/'guard.py').read_text()
        self.assertIn("require(mode in ('before-test','after-test'), 'successor03 never reruns setup')",guard)
        self.assertIn('retained_setup(config, root)',guard)
        self.assertIn("b'0\\n',b'0\\r\\n'",guard)

    def test_all_fourteen_test_semantics_and_limits_exact(self):
        a=json.loads((OLD/'manifest.json').read_bytes())
        b=json.loads((NEW/'manifest.json').read_bytes())
        self.assertEqual(len(b['jobs']),14)
        for old,new in zip(a['jobs'],b['jobs'],strict=True):
            for key in ('index','package','name','seconds','heavy_scope'):
                self.assertEqual(old[key],new[key])
            for suffix in ('sh','ps1'):
                path=f"test-{new['index']:02}.{suffix}"
                expected=(OLD/path).read_text().replace(OLD.name,NEW.name).replace(old['output'],new['output'])
                self.assertEqual((NEW/path).read_text(),expected)
            shell=(NEW/f"test-{new['index']:02}.sh").read_text()
            self.assertIn("printf '805306368\\n'",shell)
            self.assertIn('1 passed; 0 failed',shell)
            self.assertIn('test '+new['name']+' ',shell)
            self.assertTrue(new['output'].endswith('-03'))

    def test_frozen_all_shells_and_actual_drivers(self):
        inputs=json.loads((NEW/'inputs.json').read_bytes())
        for name,digest in inputs.items():
            self.assertEqual(hashlib.sha256((NEW/name).read_bytes()).hexdigest(),digest)
        shells=list(NEW.glob('*.sh'));self.assertEqual(len(shells),30)
        for path in shells:self.assertNotIn(b'\r',path.read_bytes())
        for name in ('guard.py','check-inputs.py'):
            compile((NEW/name).read_bytes(),str(NEW/name),'exec')
        recipe=json.loads((P/'transfer-v2-five-controls-execution-root-recipe-03.json').read_bytes())
        self.assertEqual(recipe['new_setup_jobs'],0)
        self.assertEqual(recipe['inputs_sha256'],hashlib.sha256((NEW/'inputs.json').read_bytes()).hexdigest())
        self.assertEqual(recipe['coordinator_sha256'],hashlib.sha256((P/recipe['coordinator']).read_bytes()).hexdigest())
