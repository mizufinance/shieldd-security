import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import decaf_field_proof
import decaf_go_proof
import decaf_proof


class ProofReportTests(unittest.TestCase):
    def test_cleanup_failure_invalidates_previous_success(self):
        for module, directory in ((decaf_proof, "decaf-proof"),
                                  (decaf_go_proof, "decaf-go-proof-replay"),
                                  (decaf_field_proof, "decaf-field-proof-replay")):
            for error in (RuntimeError("cleanup failed"), KeyboardInterrupt()):
                with self.subTest(module=module.__name__, error=type(error).__name__), tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    work = root / directory
                    (work / "old").mkdir(parents=True)
                    report = work / "report.json"
                    report.write_text('{"status":"passed","completed":true}')
                    with patch.object(module.formal, "WORK", root), \
                         patch.object(module.formal, "exclusive_lock", contextlib.nullcontext), \
                         patch.object(module.shutil, "rmtree", side_effect=error), \
                         contextlib.redirect_stdout(io.StringIO()):
                        if isinstance(error, KeyboardInterrupt):
                            with self.assertRaises(KeyboardInterrupt):
                                module.main()
                        else:
                            self.assertEqual(module.main(), 1)
                    state = json.loads(report.read_text())
                    self.assertFalse(state["completed"])
                    self.assertEqual(state["status"], "failed")
                    self.assertFalse(state["full_certification"])


if __name__ == "__main__":
    unittest.main()
