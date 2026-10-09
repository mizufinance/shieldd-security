"""Source-only genuine registry association and unchanged23+17 control payloads."""
from pathlib import Path
import hashlib,json,runpy,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
OLD=P/'transfer-coherent-controls-execution-03'
NEW=P/'transfer-coherent-controls-execution-04'
OS=P/'transfer-coherent-controls-prepare-02'
NS=P/'transfer-coherent-controls-prepare-03'

class CoherentControlsSetup06SuccessorTests(unittest.TestCase):
    def test_nine_runtime_bodies_and_semantic_descriptors_unchanged(self):
        files=list((OS/'delta').rglob('*.rs'));self.assertEqual(len(files),9)
        for path in files:self.assertEqual(path.read_bytes(),(NS/path.relative_to(OS)).read_bytes())
        for name in ('acceptance-policy-contracts.json','branch-descriptor.json','effect-descriptor.json',
                     'persistent-query-tests.json','TransferCanonicalCarrier.lean','parent-manifest.json'):
            self.assertEqual((OS/name).read_bytes(),(NS/name).read_bytes())
        old=json.loads((OLD/'manifest.json').read_bytes())
        new=json.loads((NEW/'manifest.json').read_bytes())
        self.assertEqual(len(new['jobs']),44)
        self.assertEqual(sum(j['kind']=='test'for j in new['jobs']),23)
        self.assertEqual(sum(j['kind']=='branch'for j in new['jobs']),17)
        self.assertEqual(old['budgets'],new['budgets'])
        for a,b in zip(old['jobs'],new['jobs'],strict=True):
            for key in ('index','kind','name','package','seconds'):
                self.assertEqual(a.get(key),b.get(key))
            self.assertEqual(b['output'],a['output'][:-2]+'04')
            self.assertTrue(b['output'].endswith('-04'))
        self.assertTrue(new['primary_setup_reused'])
        self.assertTrue(new['registry'].endswith('-06'))
        self.assertTrue(new['alternate_registry'].endswith('-04'))
        self.assertEqual(new['setup_output'],'transfer-v2-five-setup06-successor-02')

    def test_actual_receipts_complete_frozen_sources_and_shell_framing(self):
        for packet,name in ((NS,'packet-inputs.json'),(NEW,'inputs.json')):
            for rel,digest in json.loads((packet/name).read_bytes()).items():
                self.assertEqual(hashlib.sha256((packet/rel).read_bytes()).hexdigest(),digest)
            for path in packet.rglob('*.py'):compile(path.read_bytes(),str(path),'exec')
        config=json.loads((NEW/'manifest.json').read_bytes())
        for raw,digest in config['setup_success_inputs'].items():
            self.assertEqual(hashlib.sha256(Path(raw).read_bytes()).hexdigest(),digest)
        self.assertEqual(config['source_manifest_sha256'],hashlib.sha256((NS/'manifest.json').read_bytes()).hexdigest())
        self.assertEqual(config['source_packet_inputs_sha256'],hashlib.sha256((NS/'packet-inputs.json').read_bytes()).hexdigest())
        shells=list(NEW.glob('*.sh'));self.assertEqual(len(shells),88)
        for path in shells:self.assertNotIn(b'\r',path.read_bytes())
        stage=(NS/'stage.py').read_text();guard=(NEW/'guard.py').read_text()
        self.assertIn("recipe['setup_success_inputs']",stage)
        self.assertIn("config['setup_success_inputs']",guard)
        self.assertIn("b'0\\n',b'0\\r\\n'",stage)
        self.assertIn("setup/'task-swap-cleanup.txt'",guard)
        self.assertIn('registry06',guard)

    def test_existing_source_policy_controls_remain_executable(self):
        # Executes only artifact/refusal fixtures; never calls the native guard.
        runpy.run_path(str(NEW/'check-source.py'),run_name='__main__')

    def test_root_serial_recipe_executes_only_exact_fresh_fortyfour(self):
        recipe=json.loads((P/'transfer-coherent-controls-setup06-root-recipe-05.json').read_bytes())
        path=P/recipe['coordinator']
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),recipe['coordinator_sha256'])
        self.assertEqual(hashlib.sha256((NEW/'inputs.json').read_bytes()).hexdigest(),recipe['execution_inputs_sha256'])
        body=path.read_text()
        self.assertIn("$taskGuards=1..44|ForEach-Object {'job-{0:d2}.ps1'",body)
        self.assertIn('-ne 88',body)
        self.assertNotIn('setup06.ps1',body)
        self.assertIn('setup_success_inputs',body)
        self.assertIn(recipe['execution_inputs_sha256'],body)
