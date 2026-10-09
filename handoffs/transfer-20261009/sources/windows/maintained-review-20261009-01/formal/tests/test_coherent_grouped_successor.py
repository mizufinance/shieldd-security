"""Readiness refuses incomplete native groups and keeps original source math."""
from pathlib import Path
import hashlib,importlib.util,json,tempfile,unittest

P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
OLD=P/'transfer-coherent-controls-execution-05'
NEW=P/'transfer-coherent-controls-execution-06'
GROUP=P/'transfer-v2-five-controls-grouped-06'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

class CoherentGroupedTests(unittest.TestCase):
    def test_exact_commands_build_budgets_and_native_resource_delta(self):
        a=json.loads((OLD/'manifest.json').read_bytes());b=json.loads((NEW/'manifest.json').read_bytes())
        for key in('source_packet','source_packet_inputs_sha256','source_child','source_parent','lock_sha256','setup_success_inputs','setup_publication_sha256','cpp_version_inputs','header_compatibility','build_budgets'):
            self.assertEqual(a[key],b[key])
        self.assertEqual(b['native_budgets'],dict(a['native_budgets'],resident_MiB=4096))
        self.assertEqual(b['original_controls_prerequisite']['packet'],GROUP.name)
        self.assertEqual(len(b['jobs']),44)
        for old,new in zip(a['jobs'],b['jobs'],strict=True):
            self.assertEqual({k:v for k,v in old.items()if k!='output'},{k:v for k,v in new.items()if k!='output'})
            name=f"job-{new['index']:02}.sh"
            expected=(OLD/name).read_text().replace(OLD.name,NEW.name)
            for x,y in zip(a['jobs'],b['jobs'],strict=True):expected=expected.replace(x['output'],y['output'])
            expected=expected.replace(a['alternate_registry'],b['alternate_registry'])
            if new['kind']in('test','branch','alternate_setup'):
                expected=expected.replace("printf '3221225472\\n' > \"$cg/memory.max\"","printf '4294967296\\n' > \"$cg/memory.max\"",1)
            self.assertEqual((NEW/name).read_text(),expected)
            self.assertIn("CXXFLAGS='-include cstdint'",expected)
        for packet in(OLD,NEW):
            for name,wanted in json.loads((packet/'inputs.json').read_bytes()).items():self.assertEqual(sha(packet/name),wanted)
        for path in NEW.glob('*.sh'):self.assertNotIn(b'\r',path.read_bytes())
        self.assertEqual(len(list(NEW.glob('*.sh'))),88)
        for path in NEW.glob('*.py'):compile(path.read_bytes(),str(path),'exec')

    def test_readiness_all_three_results_and_refusals(self):
        readiness=load(NEW/'original-readiness.py','coherent_group_fixture')
        result=load(GROUP/'group-result.py','libtest_group_fixture')
        with tempfile.TemporaryDirectory()as temp:
            root=Path(temp);packet=root/GROUP.name;packet.mkdir()
            for path in GROUP.rglob('*'):
                if path.is_file():
                    target=packet/path.relative_to(GROUP);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(path.read_bytes())
            config=json.loads((NEW/'manifest.json').read_bytes());wanted=config['original_controls_prerequisite']
            coordinator=root/wanted['coordinator_source'];coordinator.write_bytes((P/wanted['coordinator_source']).read_bytes())
            serial=root/wanted['coordinator'];serial.mkdir();(serial/'complete.txt').write_bytes(b'fixture only\n')
            (serial/'completed-guards.txt').write_bytes(b'group-01.ps1\ngroup-02.ps1\ngroup-03.ps1\n')
            group_config=json.loads((packet/'manifest.json').read_bytes())
            for job in group_config['jobs']:
                out=root/job['output'];out.mkdir()
                for name in('exit.txt','wrapper-exit.txt'):(out/name).write_bytes(b'0\r\n')
                (out/'task-swap-cleanup.txt').write_bytes(b'removed\n')
                (out/'cgroup-cgroup-procs-after.txt').write_bytes(b'')
                (out/'owned-group-after.txt').write_bytes(b'')
                (out/'cgroup-memory-events-after.txt').write_bytes(b'oom 0\noom_kill 0\noom_group_kill 0\n')
                for before,after in(('full-source-before.json','full-source-after.json'),('registry-before.json','registry-after.json'),('runner-script-before.txt','runner-script-after.txt'),('source-inputs.txt','source-inputs-after.txt'),('sdk-source-before.txt','sdk-source-after.txt'),('formal-exporters-before.txt','formal-exporters-after.txt'),('app-source-before.txt','app-source-after.txt'),('setup-source-before.txt','setup-source-after.txt')):
                    for name in(before,after):(out/name).write_bytes(b'fixture identity only\n')
                (out/'rustc-version.txt').write_bytes(('release: 1.95.0\ncommit-hash: '+group_config['rust195_commit']+'\n').encode())
                count=len(job['names'])
                (out/'stdout.txt').write_bytes(f'running {count} tests\ntest result: ok. {count} passed; 0 failed; 0 ignored; 0 measured; 20 filtered out; finished in 1.0s\n'.encode())
                (out/'libtest-results.txt').write_bytes(''.join('ok '+name+'\n'for name in job['names']).encode())
                (out/'group-result.json').write_bytes(json.dumps(result.validate(packet,out)).encode())
            self.assertEqual(readiness.completed(root,config)['tests'],14)
            last=root/group_config['jobs'][-1]['output']
            saved=(last/'group-result.json').read_bytes();(last/'group-result.json').write_bytes(b'{}')
            with self.assertRaisesRegex(ValueError,'receipt changed'):readiness.completed(root,config)
            (last/'group-result.json').write_bytes(saved)
            (last/'cgroup-memory-events-after.txt').write_bytes(b'oom 1\noom_kill 0\noom_group_kill 0\n')
            with self.assertRaisesRegex(ValueError,'resource failure'):readiness.completed(root,config)
            (last/'cgroup-memory-events-after.txt').write_bytes(b'oom 0\noom_kill 0\noom_group_kill 0\n')
            (last/'libtest-results.txt').write_bytes(b'')
            with self.assertRaisesRegex(ValueError,'named results'):readiness.completed(root,config)
