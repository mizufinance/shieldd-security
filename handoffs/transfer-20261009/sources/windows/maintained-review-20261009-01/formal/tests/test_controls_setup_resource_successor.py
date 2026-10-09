"""Source-only resource/receipt successor checks; never starts WSL or native jobs."""
from pathlib import Path
import hashlib,json,unittest

P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
OLD=P/'transfer-v2-five-controls-execution-01'
NEW=P/'transfer-v2-five-controls-execution-02'

class ControlsSetupResourceSuccessorTests(unittest.TestCase):
    def test_frozen_sources_all_shell_framing_and_receipt_associations(self):
        inputs=json.loads((NEW/'inputs.json').read_bytes())
        for name,digest in inputs.items():
            self.assertEqual(hashlib.sha256((NEW/name).read_bytes()).hexdigest(),digest)
        shells=list(NEW.glob('*.sh'))
        self.assertEqual(len(shells),30)
        for path in shells:self.assertNotIn(b'\r',path.read_bytes())
        for name in ('guard.py','check-inputs.py'):
            compile((NEW/name).read_bytes(),str(NEW/name),'exec')
        config=json.loads((NEW/'manifest.json').read_bytes())
        previous=json.loads((OLD/'manifest.json').read_bytes())
        for key in ('pin','source_packet','source_packet_inputs_sha256','source_parent',
                    'source_child','setup_binary_sha256','native_setup_sources','lock_sha256'):
            self.assertEqual(config[key],previous[key])
        self.assertEqual(config['setup_output'],'transfer-v2-five-setup06-successor-02')
        self.assertTrue(config['registry'].endswith('-06'))
        for raw,digest in config['resource_failure_inputs'].items():
            self.assertEqual(hashlib.sha256(Path(raw).read_bytes()).hexdigest(),digest)
        self.assertIn('exit15',config['resource_failure_scope'])

    def test_setup_only_resource_increase_and_original_stops(self):
        config=json.loads((NEW/'manifest.json').read_bytes())
        self.assertEqual(config['budgets'],json.loads((OLD/'manifest.json').read_bytes())['budgets'])
        setup=config['setup_budgets']
        self.assertEqual((setup['resident_MiB'],setup['host_physical_admit_KiB'],
                          setup['host_commit_admit_KiB']),(3072,5767168,4718592))
        body=(NEW/'setup06.sh').read_text()
        for exact in ["printf '3221225472\\n' > \"$cg/memory.max\"",
                      '[ "$host_available" -ge 5767168 ]','[ "$commit_free" -ge 4718592 ]',
                      "printf '8589934592\\n' > \"$cg/memory.swap.max\"",
                      'fallocate -l 6442450944', 'swapon --priority -3',
                      'timeout --kill-after=10 7200','-lt 1572864','-lt 524288']:
            self.assertIn(exact,body)
        self.assertNotIn('setup05',body)
        self.assertIn('setup06-successor02',body)
        self.assertIn('.TotalSeconds -ge 7400',(NEW/'setup06.ps1').read_text())

    def test_all_fourteen_semantic_commands_and_payloads_unchanged(self):
        config=json.loads((NEW/'manifest.json').read_bytes())
        previous=json.loads((OLD/'manifest.json').read_bytes())
        for old,current in zip(previous['jobs'],config['jobs'],strict=True):
            for key in ('index','package','name','seconds','heavy_scope'):
                self.assertEqual(current[key],old[key])
            index=current['index']
            expected=(OLD/f'test-{index:02}.sh').read_text()
            expected=expected.replace('transfer-v2-five-controls-execution-01','transfer-v2-five-controls-execution-02')
            expected=expected.replace('transfer-test-pari-v2-844389-20261004-05','transfer-test-pari-v2-844389-20261004-06')
            expected=expected.replace(old['output'],current['output'])
            self.assertEqual((NEW/f'test-{index:02}.sh').read_text(),expected)
            self.assertIn("printf '805306368\\n'",expected)
            self.assertIn('1 passed; 0 failed',expected)
            self.assertIn('test '+current['name']+' ',expected)
            self.assertTrue(current['output'].endswith('-02'))
        guard=(NEW/'guard.py').read_text()
        self.assertIn("result['destination']==config['source_child']",guard)
        self.assertIn("(activated/'exit.txt').read_bytes() in (b'0\\n',b'0\\r\\n')",guard)
        self.assertIn("helpers.inventory(Path(config['source_child']))",guard)
        self.assertIn("registry_inventory(keys) == published['files']",guard)
        coordinator=(P/'root-five-controls-serial-02.ps1').read_text()
        self.assertIn('PhysicalKiB -lt 5767168',coordinator)
        self.assertIn('CommitFreeKiB -lt 4718592',coordinator)
        self.assertIn('-ne 30',coordinator)
        self.assertIn("@('setup06.ps1')+(1..14",coordinator)
