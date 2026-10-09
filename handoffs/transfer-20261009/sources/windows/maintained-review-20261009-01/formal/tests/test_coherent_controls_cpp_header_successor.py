"""Environment-only coherent successor and semantic readiness refusal fixtures."""
from pathlib import Path
import hashlib,json,runpy,tempfile,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
OLD=P/'transfer-coherent-controls-execution-04'
NEW=P/'transfer-coherent-controls-execution-05'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

class CoherentHeaderSuccessorTests(unittest.TestCase):
    def test_fortyfour_exact_commands_resources_source_and_only_header_environment(self):
        a=json.loads((OLD/'manifest.json').read_bytes());b=json.loads((NEW/'manifest.json').read_bytes())
        for key in ('source_packet','source_manifest_sha256','source_packet_inputs_sha256','source_parent','source_child','registry','setup_output','setup_success_inputs','setup_publication_sha256','budgets','lock_sha256','pin'):
            self.assertEqual(a[key],b[key])
        self.assertEqual(len(b['jobs']),44)
        self.assertEqual(sum(j['kind']=='test'for j in b['jobs']),23)
        self.assertEqual(sum(j['kind']=='branch'for j in b['jobs']),17)
        substitutions=[(OLD.name,NEW.name),(a['alternate_registry'],b['alternate_registry'])]
        substitutions.extend((x['output'],y['output'])for x,y in zip(a['jobs'],b['jobs'],strict=True))
        for x,y in zip(a['jobs'],b['jobs'],strict=True):
            self.assertEqual({k:v for k,v in x.items()if k!='output'},{k:v for k,v in y.items()if k!='output'})
            for name in (f"job-{y['index']:02}.sh",f"job-{y['index']:02}.ps1",f"cleanup-job-{y['index']:02}.sh"):
                expected=(OLD/name).read_text()
                for before,after in substitutions:expected=expected.replace(before,after)
                if name.startswith('job-')and name.endswith('.sh'):
                    expected=expected.replace('export CARGO_BUILD_JOBS=1\n',"export CARGO_BUILD_JOBS=1\nexport CXXFLAGS='-include cstdint'\n",1)
                    if y['kind']in('test','branch','alternate_setup'):
                        expected=expected.replace("printf '805306368\\n' > \"$cg/memory.max\"","printf '3221225472\\n' > \"$cg/memory.max\"",1)
                        expected=expected.replace('[ "$host_available" -ge 3145728 ] && [[ "$commit_free" =~ ^[0-9]+$ ]] && [ "$commit_free" -ge 1572864 ]','[ "$host_available" -ge 5767168 ] && [[ "$commit_free" =~ ^[0-9]+$ ]] && [ "$commit_free" -ge 4718592 ]',1)
                if name.startswith('job-')and name.endswith('.ps1')and y['kind']in('test','branch','alternate_setup'):
                    expected=expected.replace('$taskMemoryHelperDigest=',"$taskAdmission=Get-TaskMemorySnapshot\nif($taskAdmission.PhysicalKiB -lt 5767168 -or $taskAdmission.CommitFreeKiB -lt 4718592){throw '3GiB native test/example admission before WSL'}\n$taskMemoryHelperDigest=",1)
                self.assertEqual((NEW/name).read_text(),expected)
            self.assertEqual((NEW/f"job-{y['index']:02}.sh").read_text().count('CXXFLAGS'),1)
        self.assertTrue(b['primary_setup_reused'])
        self.assertEqual(b['alternate_registry'],a['alternate_registry'][:-2]+'05')

    def test_frozen_receipts_compiler_and_preexecution_readiness(self):
        config=json.loads((NEW/'manifest.json').read_bytes())
        self.assertEqual(config['build_budgets'],json.loads((OLD/'manifest.json').read_bytes())['budgets'])
        self.assertEqual(config['native_budgets']['resident_MiB'],3072)
        self.assertEqual(config['native_budgets']['host_physical_admit_KiB'],5767168)
        self.assertEqual(config['native_budgets']['host_commit_admit_KiB'],4718592)
        for category in ('setup_success_inputs','cpp_version_inputs','test_failure_inputs','previous_test_failure_inputs','resource_failure_inputs'):
            for raw,digest in config[category].items():self.assertEqual(sha(raw),digest)
        for name,digest in json.loads((NEW/'inputs.json').read_bytes()).items():self.assertEqual(sha(NEW/name),digest)
        for path in NEW.glob('*.py'):compile(path.read_bytes(),str(path),'exec')
        shells=list(NEW.glob('*.sh'));self.assertEqual(len(shells),88)
        for path in shells:self.assertNotIn(b'\r',path.read_bytes())
        recipe=json.loads((P/'transfer-coherent-controls-header-root-recipe-06.json').read_bytes())
        self.assertEqual(sha(P/recipe['coordinator']),recipe['coordinator_sha256'])
        self.assertEqual(sha(NEW/'inputs.json'),recipe['execution_inputs_sha256'])
        body=(P/recipe['coordinator']).read_text()
        self.assertLess(body.index('original-readiness.py'),body.index('& \'C:/Windows/System32/wsl.exe\''))
        self.assertIn('retained_cpp(config)',(NEW/'guard.py').read_text())
        self.assertIn("original_controls_readiness').completed(root,config)",(NEW/'guard.py').read_text())
        # Independent app-build success does not satisfy the 14-test prerequisite.
        fn=runpy.run_path(str(NEW/'original-readiness.py'))['completed']
        with tempfile.TemporaryDirectory()as temp:
            root=Path(temp);packet=root/'original';packet.mkdir()
            (packet/'inputs.json').write_bytes(b'{}');(root/'coordinator.ps1').write_bytes(b'exact')
            cfg={'original_controls_prerequisite':{'packet':'original','inputs_sha256':sha(packet/'inputs.json'),
                'coordinator_source':'coordinator.ps1','coordinator_source_sha256':sha(root/'coordinator.ps1'),'coordinator':'serial'}}
            (root/'successful-app-build').mkdir()
            with self.assertRaisesRegex(ValueError,'complete actual original14'):fn(root,cfg)
            (root/'serial').mkdir();(root/'serial/complete.txt').write_bytes(b'claimed')
            (root/'serial/completed-guards.txt').write_bytes(b'test-01.ps1\n')
            with self.assertRaisesRegex(ValueError,'all14 exact original guards'):fn(root,cfg)
