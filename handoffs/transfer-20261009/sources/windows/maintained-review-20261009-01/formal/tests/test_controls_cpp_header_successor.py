"""Header environment only: unchanged commands, setup, locks and resource limits."""
from pathlib import Path
import hashlib,json,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
OLD=P/'transfer-v2-five-controls-execution-03'
NEW=P/'transfer-v2-five-controls-execution-04'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

class ControlsCppHeaderSuccessorTests(unittest.TestCase):
    def test_all_fourteen_exact_commands_and_only_header_flag(self):
        a=json.loads((OLD/'manifest.json').read_bytes());b=json.loads((NEW/'manifest.json').read_bytes())
        for key in ('registry','setup_output','pin','source_packet','source_packet_inputs_sha256','source_child','source_parent','setup_binary_sha256','native_setup_sources','lock_sha256','budgets','setup_budgets','setup_success_inputs','setup_publication_sha256'):
            self.assertEqual(a[key],b[key])
        self.assertEqual(len(b['jobs']),14)
        for old,new in zip(a['jobs'],b['jobs'],strict=True):
            self.assertEqual({k:v for k,v in old.items() if k!='output'},{k:v for k,v in new.items() if k!='output'})
            for suffix in ('sh','ps1'):
                filename=f"test-{new['index']:02}.{suffix}"
                expected=(OLD/filename).read_text().replace(OLD.name,NEW.name).replace(old['output'],new['output'])
                if suffix=='sh':expected=expected.replace('export CARGO_BUILD_JOBS=1\n',"export CARGO_BUILD_JOBS=1\nexport CXXFLAGS='-include cstdint'\n",1)
                self.assertEqual((NEW/filename).read_text(),expected)
            shell=(NEW/f"test-{new['index']:02}.sh").read_text()
            self.assertEqual(shell.count('CXXFLAGS'),1)
            self.assertIn('cargo test --locked --offline --profile ci',shell)
            self.assertIn('test '+new['name']+' ',shell)
            self.assertIn("printf '805306368\\n'",shell)
            self.assertTrue(new['output'].endswith('-04'))
        coordinator=(P/'root-five-controls-serial-04.ps1').read_text()
        self.assertIn("$taskGuards=1..14|ForEach-Object",coordinator)
        self.assertNotIn("@('setup06.ps1')",coordinator)

    def test_actual_compiler_failure_and_frozen_receipts(self):
        config=json.loads((NEW/'manifest.json').read_bytes())
        for category in ('setup_success_inputs','cpp_version_inputs','test_failure_inputs','previous_test_failure_inputs'):
            for path,digest in config[category].items():self.assertEqual(sha(path),digest)
        self.assertEqual(config['header_compatibility']['value'],'-include cstdint')
        self.assertEqual(config['header_compatibility']['version'],'c++ (Ubuntu 15.2.0-16ubuntu1) 15.2.0')
        self.assertIn('retained_cpp(config)',(NEW/'guard.py').read_text())
        self.assertIn("'compiler_sha256'",(NEW/'guard.py').read_text())
        inputs=json.loads((NEW/'inputs.json').read_bytes())
        for name,digest in inputs.items():self.assertEqual(sha(NEW/name),digest)
        shells=list(NEW.glob('*.sh'));self.assertEqual(len(shells),30)
        for path in shells:self.assertNotIn(b'\r',path.read_bytes())
        for name in ('guard.py','check-inputs.py'):compile((NEW/name).read_bytes(),str(NEW/name),'exec')
        recipe=json.loads((P/'transfer-v2-five-controls-execution-root-recipe-04.json').read_bytes())
        self.assertEqual(recipe['new_setup_jobs'],0)
        self.assertEqual(recipe['inputs_sha256'],sha(NEW/'inputs.json'))
        self.assertEqual(recipe['coordinator_sha256'],sha(P/recipe['coordinator']))
