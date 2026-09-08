import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import decoder_contract
import security


class DecoderToolingTests(unittest.TestCase):
    def test_exact_runtime_sources_are_copied_and_hashed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source" / decoder_contract.BOUNDARY
            source.mkdir(parents=True)
            for name in ("aggregate_proof_wrapper", "canonical_encoding"):
                (source / f"{name}.rs").write_text(f"// exact {name}\n")
            crate = root / "crate"
            hashes = decoder_contract.prepare(root / "source", crate)
            for path, checksum in hashes.items():
                self.assertEqual((root / "source" / path).read_bytes(), (crate / "src" / Path(path).name).read_bytes())
                self.assertEqual(checksum, security.formal.file_digest(crate / "src" / Path(path).name))

    def test_bootstrap_failure_writes_failed_report(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(security.formal, "WORK", root / "work"), \
                 patch.object(security.formal, "CACHE", root / "cache"), \
                 patch.object(security.formal, "resolve_inputs", side_effect=RuntimeError("missing candidate")):
                with self.assertRaisesRegex(RuntimeError, "missing candidate"):
                    security.fuzz_locked(argparse.Namespace(seconds=1))
            report = json.loads((root / "work/fuzz-report/report.json").read_text())
            self.assertEqual(report["status"], "failed")
            self.assertFalse(report["full_certification"])
            self.assertIsNone(report["candidate_revision"])

    def test_nonzero_fuzzer_exit_is_a_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            corpus, reports = root / "corpus", root / "reports"
            corpus.mkdir()
            reports.mkdir()
            with self.assertRaisesRegex(RuntimeError, "failed"):
                security.bounded_run([sys.executable, "-c", "raise SystemExit(7)"], root, None, reports / "log", corpus, reports, 10)

    def test_output_budget_is_enforced_even_when_process_exits(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            corpus, reports = root / "corpus", root / "reports"
            corpus.mkdir()
            reports.mkdir()
            (corpus / "seed").write_bytes(b"0123456789")
            with patch.object(security, "BYTE_LIMIT", 1), self.assertRaisesRegex(RuntimeError, "exceeded"):
                security.bounded_run([sys.executable, "-c", "pass"], root, None, reports / "log", corpus, reports, 10)


if __name__ == "__main__":
    unittest.main()
