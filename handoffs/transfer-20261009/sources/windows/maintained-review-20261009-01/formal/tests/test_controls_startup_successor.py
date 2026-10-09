"""Fresh startup margin preserves real app results and every workload bound."""
from pathlib import Path
import hashlib,json,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
OLD=P/'transfer-v2-five-controls-remaining-groups-07'
NEW=P/'transfer-v2-five-controls-remaining-groups-09'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
class StartupControlsTests(unittest.TestCase):
    def test_retained_success_and_failed_admission_have_distinct_credit(self):
        old=json.loads((OLD/'manifest.json').read_bytes());new=json.loads((NEW/'manifest.json').read_bytes())
        self.assertEqual(old['retained_app'],new['retained_app'])
        self.assertEqual(old['jobs'][0],new['jobs'][0])
        self.assertEqual(old['original_exact_jobs'],new['original_exact_jobs'])
        self.assertEqual(old['budgets'],new['budgets'])
        for raw,h in new['failed_admission07'].items():self.assertEqual(sha(raw),h)
        self.assertEqual(new['resident_admission'],dict(physical_KiB=5767168,commit_KiB=4718592,fresh_consecutive_samples=3,wait_seconds=300))
        self.assertGreater(new['startup_admission']['physical_KiB'],5767168)
        self.assertGreater(new['startup_admission']['commit_KiB'],4718592)
    def test_only_admission_wait_and_owned_namespace_change(self):
        for i in(2,3):
            body=(NEW/f'group-{i:02}.sh').read_text()
            before=(OLD/f'group-{i:02}.sh').read_text()
            restored=body.replace(NEW.name,OLD.name).replace(f'control-group-{i:02}-09',f'control-group-{i:02}-07')
            restored=restored.replace('SECONDS-preflight_start))" -ge 300','SECONDS-preflight_start))" -ge 150')
            self.assertEqual(restored,before)
            self.assertIn('"$host_available" -ge 5767168',body)
            self.assertIn('"$commit_free" -ge 4718592',body)
            self.assertIn('"$ready" -lt 3',body)
            ps=(NEW/f'group-{i:02}.ps1').read_text()
            self.assertLess(ps.index('-ge 7077888'),ps.index('New-Item -ItemType Directory -Path $taskPacket |'))
            self.assertIn('.TotalSeconds -ge 1350',ps)
            self.assertIn('.TotalSeconds -ge 300',ps)
        for path in NEW.glob('*.sh'):self.assertNotIn(b'\r',path.read_bytes())
        for path in NEW.glob('*.py'):compile(path.read_bytes(),str(path),'exec')
        for n,h in json.loads((NEW/'inputs.json').read_bytes()).items():self.assertEqual(sha(NEW/n),h)
        coordinator=(P/'root-five-controls-remaining-groups-09.ps1').read_text()
        self.assertIn('$taskGuards=2..3',coordinator)
        self.assertIn('failed_admission07.PSObject.Properties',coordinator)
        self.assertNotIn('$taskGuards=1..3',coordinator)
