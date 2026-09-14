import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch
from contextlib import nullcontext
import json
import copy

import formal
import decaf_go_arm64_qualify as qualify


class GoArmQualificationTests(unittest.TestCase):
    def test_harness_controls_keep_both_native_operations(self):
        for case in qualify.CASES:
            text = qualify.harness(case)
            self.assertEqual(text.count("fiat.FqMul(&outputFq,&a,&b)"), 1)
            self.assertEqual(text.count("fiat.FrMul(&outputFr,&a,&b)"), 1)
        self.assertNotIn("if secret", qualify.harness("original"))
        self.assertIn("if secret", qualify.harness("branch"))
        self.assertIn("table[secret[0]&1]", qualify.harness("address"))
        with self.assertRaises(ValueError):
            qualify.harness("omitted-dependency")

    def test_config_has_independent_secret_buffer_and_single_boundary(self):
        cfg = qualify.configuration(0x100, 0x200, 0x300)
        self.assertIn("@[0x300, 64] := secret", cfg)
        self.assertEqual(cfg.count("halt at"), 1)
        self.assertNotIn("assume", cfg)
        self.assertIn("explore all", cfg)
        with self.assertRaises(ValueError):
            qualify.configuration(1, 1, 2)

    def test_symbol_ambiguity_is_rejected(self):
        self.assertEqual(qualify.symbol("  12 T main.decafDone\n", "main.decafDone"), 18)
        for text in ("", "12 T main.decafDone\n13 T main.decafDone\n"):
            with self.assertRaises(ValueError):
                qualify.symbol(text, "main.decafDone")

    def test_control_requires_complete_exploration_and_correct_leak(self):
        reached = ("[sse:result] Path 1 reached address 0x200\n"
                   "total paths 1\ncompleted/cut paths 1\npending paths 0\n"
                   "discontinued paths 0\nfailed assertions 0\n")
        secure = "Program status is : secure\n"
        insecure = "Program status is : insecure\ncontrol flow leak\n"
        qualify.classify(reached + secure, "original", 0x200)
        qualify.classify(reached + insecure, "branch", 0x200)
        for output, case in ((secure, "original"), (insecure, "branch"),
                             (reached + insecure, "address"),
                             (reached.replace("pending paths 0", "pending paths 1") + insecure, "branch"),
                             (reached.replace("total paths 1", "total paths 2") + secure, "original"),
                             (reached + insecure + "Exploration is incomplete", "branch"),
                             (reached + secure + "unknown instruction", "original")):
            with self.assertRaises(ValueError):
                qualify.classify(output, case, 0x200)

    def test_artifact_mutations_and_omissions_fail(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "binary"
            path.write_bytes(b"original")
            hashes = {str(path): formal.file_digest(path)}
            qualify.check_hashes(hashes)
            path.write_bytes(b"mutant")
            with self.assertRaises(ValueError):
                qualify.check_hashes(hashes)
            path.unlink()
            with self.assertRaises(ValueError):
                qualify.check_hashes(hashes)

    def test_missing_toolchain_invalidates_old_success(self):
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            directory = work / "decaf-go-arm64-qualification"
            directory.mkdir()
            report_path = directory / "report.json"
            report_path.write_text('{"status":"passed","completed":true}')
            with patch.object(formal, "WORK", work), patch.object(formal, "exclusive_lock", return_value=nullcontext()), \
                    patch("sys.argv", ["qualify", "--goroot", str(work / "missing"), "--dune-root", str(work)]):
                self.assertEqual(qualify.main(), 1)
            report = json.loads(report_path.read_text())
            self.assertEqual(report["status"], "blocked")
            self.assertFalse(report["completed"])
            self.assertFalse(report["full_certification"])

    def test_parent_rejects_missing_cases_and_stale_identities(self):
        matrix = {"targets": ["x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu"]}
        cases = [{"id": f"{target}-{number}", "status": "passed", "binary_sha256": "digest", "config_sha256": "digest"}
                 for target in matrix["targets"] for number in range(3)]
        cases += [{"id": "rust-fq-add-" + target, "status": "passed", "binary_sha256": "digest", "config_sha256": "digest"}
                  for target in matrix["targets"]]
        parent = {"status": "passed", "completed": True, "full_certification": False,
                  "qualification_complete": False, "cases": cases,
                  "candidate_source": {"patch_sha256": "digest"},
                  "rust_source": {"harness_sha256": "digest"},
                  "candidate_tools": {"binsec": {}, "z3": {}},
                  "candidate_components": {"plugin.so": "digest"}}
        keys = ("matrix_sha256", "runner_sha256", "classifier_sha256", "process_runner_sha256",
                "source_sha256", "proof_toolchain_sha256")
        parent.update({key: "digest" for key in keys})
        # This fixture checks receipt structure and invalidation, not analyzer validity.
        with patch.object(formal, "file_digest", return_value="digest"):
            qualify.validate_parent(parent, matrix)
            mutants = []
            for key in keys:
                mutant = copy.deepcopy(parent)
                mutant[key] = "stale"
                mutants.append(mutant)
            for transform in (lambda value: value["cases"].pop(),
                              lambda value: value["cases"][0].update(binary_sha256="stale"),
                              lambda value: value["candidate_components"].clear(),
                              lambda value: value["candidate_tools"].pop("z3")):
                mutant = copy.deepcopy(parent)
                transform(mutant)
                mutants.append(mutant)
            for mutant in mutants:
                with self.assertRaises(ValueError):
                    qualify.validate_parent(mutant, matrix)
