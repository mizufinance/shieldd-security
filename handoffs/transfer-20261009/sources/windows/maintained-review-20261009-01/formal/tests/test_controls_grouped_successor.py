"""Exact three-process grouping keeps the fourteen native assertions intact."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import unittest

P = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
NEW = P / 'transfer-v2-five-controls-grouped-06'
OLD = P / 'transfer-v2-five-controls-execution-05'

class GroupedControlsTests(unittest.TestCase):
    def test_strict_named_results_and_refusals(self):
        spec = importlib.util.spec_from_file_location('group_result_fixture', NEW / 'group-result.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        names = ['module::positive', 'module::reject_stale', 'module::readback']
        summary = 'running 3 tests\ntest result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 20 filtered out; finished in 2.10s\n'
        log = b'ok module::readback\nok module::positive\nok module::reject_stale\n'
        self.assertEqual(set(module.parse(log, summary, names)), set(names))
        self.assertEqual(set(module.parse(log.replace(b'\n', b'\r\n'), summary.replace('\n', '\r\n'), names)), set(names))
        for bad in (log + b'ok module::positive\n', log + b'ok module::unselected\n', log.replace(b'ok module::positive\n', b''), log.replace(b'ok module::positive', b'ignored module::positive'), b''):
            with self.assertRaises(ValueError): module.parse(bad, summary, names)
        for bad in (summary + summary, summary.replace('3 passed', '2 passed'), summary.replace('0 ignored', '1 ignored'), summary.replace('running 3', 'running 4'), ''):
            with self.assertRaises(ValueError): module.parse(log, bad, names)

    def test_commands_exact_inventory_resources_and_frozen_defaults(self):
        a = json.loads((OLD / 'manifest.json').read_bytes())
        b = json.loads((NEW / 'manifest.json').read_bytes())
        self.assertEqual(b['original_exact_jobs'], a['jobs'])
        self.assertEqual([name for job in b['jobs'] for name in job['names']], [job['name'] for job in a['jobs']])
        self.assertEqual([len(job['names']) for job in b['jobs']], [5, 6, 3])
        for key in ('registry', 'setup_output', 'source_child', 'source_packet', 'source_packet_inputs_sha256', 'setup_success_inputs', 'setup_publication_sha256', 'lock_sha256'):
            self.assertEqual(a[key], b[key])
        self.assertEqual(b['budgets'], dict(a['budgets'], resident_MiB=4096))
        for i, job in enumerate(b['jobs'], 1):
            shell = (NEW / f'group-{i:02}.sh').read_text()
            commands = re.findall(r'^setsid bash -c .*cargo test.*$', shell, re.M)
            self.assertEqual(len(commands), 1)
            command = commands[0]
            for name in job['names']: self.assertEqual(command.count(name), 1)
            self.assertIn('--lib -- ' + ' '.join(job['names']) + ' --exact --test-threads=1', command)
            self.assertIn('--logfile "$3/libtest-results.txt"', command)
            self.assertIn('"$first_cpu" "$out"', command)
            self.assertIn("printf '4294967296\\n'", shell)
            self.assertIn("printf '8589934592\\n'", shell)
            self.assertIn('fallocate -l 6442450944', shell)
            self.assertIn('"$host_available" -lt 1572864', shell)
            self.assertIn('"$commit_free" -lt 524288', shell)
            self.assertIn(str(job['seconds']) + ' /usr/bin/time', shell)
            self.assertIn('release: 1.95.0', shell)
            self.assertIn('RUSTC_BOOTSTRAP', shell)
            self.assertIn('-j1', command)
            self.assertNotIn('missing-one-exact-test', shell)
        for packet in (OLD, NEW):
            for name, digest in json.loads((packet / 'inputs.json').read_bytes()).items():
                self.assertEqual(hashlib.sha256((packet / name).read_bytes()).hexdigest(), digest)
        self.assertEqual(len(list(NEW.glob('*.sh'))), 6)
        for path in NEW.glob('*.sh'): self.assertNotIn(b'\r', path.read_bytes())
        for path in NEW.rglob('*.py'): compile(path.read_bytes(), str(path), 'exec')
