"""Successful app leaf is retained; remaining native jobs stay genuinely fresh."""
from pathlib import Path
import hashlib,importlib.util,json,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
NEW=P/'transfer-v2-five-controls-remaining-groups-07'
OLD=P/'transfer-v2-five-controls-grouped-06'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
class RemainingGroupsTests(unittest.TestCase):
    def test_actual_app_readback_and_refusal_identity(self):
        spec=importlib.util.spec_from_file_location('retained_app_fixture',NEW/'retained-app.py')
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        result=module.completed(NEW)
        self.assertEqual(len(result['names']),5)
        self.assertFalse(result['qualification'])
        self.assertFalse(result['certification'])
        # Actual parent receipts are read-only; malformed zero framing is tested
        # on the parser's separate source fixtures, never by modifying that leaf.
        cfg=json.loads((NEW/'manifest.json').read_bytes())
        for path,h in cfg['retained_app']['receipt_inputs'].items():self.assertEqual(sha(path),h)

    def test_admission_before_new_output_and_fixed_budget(self):
        a=json.loads((OLD/'manifest.json').read_bytes());b=json.loads((NEW/'manifest.json').read_bytes())
        self.assertEqual(a['budgets'],b['budgets'])
        self.assertEqual(a['original_exact_jobs'],b['original_exact_jobs'])
        self.assertEqual(a['jobs'][0],b['jobs'][0])
        self.assertEqual(len(list(NEW.glob('group-*.ps1'))),2)
        for i in(2,3):
            body=(NEW/f'group-{i:02}.ps1').read_text()
            self.assertLess(body.index('$taskAdmissionStart='),body.index('New-Item -ItemType Directory -Path $taskPacket |'))
            self.assertLess(body.index('unchanged5.5phys4.5commit native admission qualified'),body.index('Start-Process'))
            self.assertIn('.TotalSeconds -ge 180',body)
            self.assertIn('-ge 5767168',body);self.assertIn('-ge 4718592',body)
            self.assertIn('$taskPacket-admission',body)
            shell=(NEW/f'group-{i:02}.sh').read_text()
            self.assertIn("printf '4294967296\\n'",shell)
            self.assertIn("printf '8589934592\\n'",shell)
            self.assertIn('"$host_available" -lt 1572864',shell)
            self.assertIn('"$commit_free" -lt 524288',shell)
            self.assertIn('900 /usr/bin/time',shell)
        for path in NEW.glob('*.sh'):self.assertNotIn(b'\r',path.read_bytes())
        self.assertEqual(len(list(NEW.glob('*.sh'))),4)
        for path in NEW.glob('*.py'):compile(path.read_bytes(),str(path),'exec')
        coordinator=(P/'root-five-controls-remaining-groups-07.ps1').read_text()
        self.assertIn('$taskGuards=2..3',coordinator)
        self.assertNotIn('$taskGuards=1..3',coordinator)
        for packet in(OLD,NEW):
            for name,h in json.loads((packet/'inputs.json').read_bytes()).items():self.assertEqual(sha(packet/name),h)
