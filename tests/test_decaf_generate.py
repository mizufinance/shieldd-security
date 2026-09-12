from contextlib import nullcontext
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import decaf_generate


class GenerationReportTests(unittest.TestCase):
    def test_failed_rerun_replaces_old_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            work = root / "work/decaf-fields"
            work.mkdir(parents=True)
            report = work / "report.json"
            report.write_text('{"status":"generated","completed":true}')
            with patch.multiple(decaf_generate.formal, ROOT=root, CACHE=root / "cache", WORK=root / "work"), \
                    patch.object(decaf_generate.formal, "exclusive_lock", nullcontext):
                self.assertEqual(decaf_generate.main(), 1)
            self.assertFalse(json.loads(report.read_text())["completed"])

    def test_interrupted_rerun_cannot_retain_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = root / "decaf/proofs/toolchain.json"
            config.parent.mkdir(parents=True)
            config.write_text('{}')
            with patch.multiple(decaf_generate.formal, ROOT=root, CACHE=root / "cache", WORK=root / "work"), \
                    patch.object(decaf_generate.formal, "exclusive_lock", nullcontext), \
                    patch.object(decaf_generate.json, "loads", side_effect=KeyboardInterrupt):
                with self.assertRaises(KeyboardInterrupt):
                    decaf_generate.main()
            report = json.loads((root / "work/decaf-fields/report.json").read_text())
            self.assertFalse(report["completed"])
            self.assertEqual(report["status"], "failed")
