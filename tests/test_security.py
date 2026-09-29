import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import security

class IdentityTests(unittest.TestCase):
    def test_duplicate_identity_key_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "lock.json"
            path.write_text('{"sha":"a","sha":"b"}')
            with self.assertRaisesRegex(security.CheckError, "duplicate"):
                security.read_json(path)

    def test_branch_name_is_not_a_pin(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "shieldd.lock").write_text(json.dumps({"sha":"dev","ref":"dev"}))
            with self.assertRaisesRegex(security.CheckError, "full lowercase"):
                security.locked_sha(root)

    def test_runtime_dirty_or_wrong_commit_rejected(self):
        with patch.object(security, "run", return_value="b" * 40):
            with self.assertRaisesRegex(security.CheckError, "differs"):
                security.runtime_identity(Path.cwd(), "a" * 40)
        with patch.object(security, "run", side_effect=["a" * 40, " M src/lib.rs"]):
            with self.assertRaisesRegex(security.CheckError, "dirty"):
                security.runtime_identity(Path.cwd(), "a" * 40)

    def test_missing_family_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "shieldd.lock").write_bytes((security.ROOT / "shieldd.lock").read_bytes())
            register = security.read_json(security.ROOT / "assurance.json")
            del register["families"]["seizure"]
            (root / "assurance.json").write_text(json.dumps(register))
            with self.assertRaisesRegex(security.CheckError, "nine"):
                security.check_register(root)

    def test_failed_promotion_preserves_previous_result(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "result.json"
            path.write_text('{"old":true}')
            with patch.object(security.os, "replace", side_effect=OSError("blocked")):
                with self.assertRaises(OSError):
                    security.write_result(path, {"new": True})
            self.assertEqual(json.loads(path.read_text()), {"old": True})
            self.assertEqual(list(path.parent.iterdir()), [path])

    def test_required_obligations_cannot_disappear(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "shieldd.lock").write_bytes((security.ROOT / "shieldd.lock").read_bytes())
            register = security.read_json(security.ROOT / "assurance.json")
            del register["claims"]["system"]
            (root / "assurance.json").write_text(json.dumps(register))
            with self.assertRaisesRegex(security.CheckError, "required assurance"):
                security.check_register(root)

    def test_family_status_cannot_claim_pilot_certification(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "shieldd.lock").write_bytes((security.ROOT / "shieldd.lock").read_bytes())
            register = security.read_json(security.ROOT / "assurance.json")
            register["families"]["transfer"] = "proved"
            (root / "assurance.json").write_text(json.dumps(register))
            with self.assertRaisesRegex(security.CheckError, "whole-family"):
                security.check_register(root)

    def test_adapter_cannot_override_receipt_identity(self):
        identity = {"sha":"a"*40}
        with patch.object(security, "runtime_identity", return_value=identity), patch.object(security, "source_identity", return_value={"dirty": True}), patch.object(Path, "is_file", return_value=True), patch.object(security, "run", return_value='{"outcome":"passed","runtime":{"sha":"forged"},"security":{"dirty":false}}'):
            result = security.execute_pilot("circuits", security.ROOT / ".work/shieldd-current")
        self.assertEqual(result["runtime"], identity)
        self.assertTrue(result["security"]["dirty"])

    def test_source_drift_during_run_discards_result(self):
        with patch.object(security, "runtime_identity", return_value={"sha":"a"*40}), patch.object(security, "source_identity", side_effect=[{"sha256":"before"},{"sha256":"after"}]), patch.object(Path, "is_file", return_value=True), patch.object(security, "run", return_value='{"outcome":"passed"}'):
            with self.assertRaisesRegex(security.CheckError, "changed during"):
                security.execute_pilot("circuits", security.ROOT / ".work/shieldd-current")

    def test_pilot_cannot_name_a_different_checkout_than_cargo(self):
        with self.assertRaisesRegex(security.CheckError, "Cargo dependencies"):
            security.execute_pilot("circuits", Path.cwd())

    def test_timeout_stops_child_process(self):
        import subprocess
        import sys
        import time
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "orphan.txt"
            child = "import time; from pathlib import Path; time.sleep(1.2); Path(" + repr(str(marker)) + ").write_text('orphan')"
            parent = "import subprocess,sys,time; subprocess.Popen([sys.executable,'-c'," + repr(child) + "]); time.sleep(10)"
            with self.assertRaises(subprocess.TimeoutExpired):
                security.run([sys.executable, "-c", parent], timeout=0.3)
            time.sleep(1.3)
            self.assertFalse(marker.exists(), "timed-out verifier left an active child")

    @unittest.skipIf(security.os.name == "nt", "POSIX process-group regression")
    def test_nested_runner_remains_in_outer_timeout_group(self):
        import subprocess
        import sys
        import time
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "orphan.txt"
            child = "import time; from pathlib import Path; time.sleep(1.2); Path(" + repr(str(marker)) + ").write_text('orphan')"
            adapter = "import security,sys; security.run([sys.executable,'-c'," + repr(child) + "], timeout=10, check=False)"
            with self.assertRaises(subprocess.TimeoutExpired):
                security.run([sys.executable, "-c", adapter], timeout=0.3)
            time.sleep(1.3)
            self.assertFalse(marker.exists(), "nested runner escaped outer timeout group")

    def test_expected_semantic_failure_can_be_inspected(self):
        import sys
        result = security.run([sys.executable, "-c", "import sys; print('semantic rejection'); sys.exit(7)"], check=False)
        self.assertEqual(result.returncode, 7)
        self.assertEqual(result.stdout.strip(), "semantic rejection")

    def test_model_only_cannot_replace_full_runtime_evidence(self):
        with patch.object(security, 'runtime_identity', return_value={'sha':'a'*40}), patch.object(security, 'source_identity', return_value={'dirty':True}), patch.object(Path, 'is_file', return_value=True), patch.object(security, 'run', return_value='{"outcome":"passed","runtime":null}'):
            with self.assertRaisesRegex(security.CheckError, 'actual runtime evidence'):
                security.execute_pilot('state', security.ROOT / '.work/shieldd-current')
            result = security.execute_pilot('state', security.ROOT / '.work/shieldd-current', model_only=True)
        self.assertEqual(result['pilot'], 'state-model')
        self.assertEqual(result['command'][-1], '--model-only')
