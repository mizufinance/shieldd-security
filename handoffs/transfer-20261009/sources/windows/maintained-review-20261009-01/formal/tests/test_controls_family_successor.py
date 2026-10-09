"""SCT/query memory family differs from retained proving app, not its tests."""
from pathlib import Path
import hashlib,json,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
OLD=P/'transfer-v2-five-controls-remaining-groups-09'
NEW=P/'transfer-v2-five-controls-remaining-groups-10'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
class FamilyControlsTests(unittest.TestCase):
    def test_family_limits_and_exact_results_are_separate(self):
        old=json.loads((OLD/'manifest.json').read_bytes());new=json.loads((NEW/'manifest.json').read_bytes())
        self.assertEqual(old['retained_app'],new['retained_app'])
        self.assertEqual(old['jobs'][0],new['jobs'][0])
        self.assertEqual(old['original_exact_jobs'],new['original_exact_jobs'])
        self.assertEqual(new['remaining_family_budgets']['resident_MiB'],2048)
        self.assertEqual(new['remaining_family_budgets']['host_physical_stop_KiB'],1572864)
        self.assertEqual(new['remaining_family_budgets']['host_commit_stop_KiB'],524288)
        self.assertEqual((NEW/'retained-app.py').read_bytes(),(OLD/'retained-app.py').read_bytes())
        for raw,h in new['failed_admission09'].items():self.assertEqual(sha(raw),h)
    def test_only_family_admission_limit_and_fresh_namespace_change(self):
        for i in(2,3):
            now=(NEW/f'group-{i:02}.sh').read_text()
            old=(OLD/f'group-{i:02}.sh').read_text()
            restored=now.replace(NEW.name,OLD.name).replace(f'control-group-{i:02}-10',f'control-group-{i:02}-09')
            restored=restored.replace("printf '2147483648\\n'","printf '4294967296\\n'")
            restored=restored.replace('"$host_available" -ge 4718592','"$host_available" -ge 5767168')
            restored=restored.replace('"$commit_free" -ge 3670016','"$commit_free" -ge 4718592')
            self.assertEqual(restored,old)
            self.assertIn('"$host_available" -lt 1572864',now)
            self.assertIn('"$commit_free" -lt 524288',now)
            self.assertIn('900 /usr/bin/time',now)
            self.assertIn("printf '8589934592\\n'",now)
            self.assertIn('"$ready" -lt 3',now)
            front=(NEW/f'group-{i:02}.ps1').read_text()
            self.assertIn('-ge 6291456 -and $taskAdmission.CommitFreeKiB -ge 5242880',front)
        for n,h in json.loads((NEW/'inputs.json').read_bytes()).items():self.assertEqual(sha(NEW/n),h)
        for path in NEW.glob('*.sh'):self.assertNotIn(b'\r',path.read_bytes())
        for path in NEW.glob('*.py'):compile(path.read_bytes(),str(path),'exec')
