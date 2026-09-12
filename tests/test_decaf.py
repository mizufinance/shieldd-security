import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import decaf


class DecafPilotTests(unittest.TestCase):
    def test_missing_dependency_is_rejected(self):
        inputs = json.loads(decaf.INPUTS.read_text())
        del inputs["libraries"]["go"]["candidate"]
        with self.assertRaisesRegex(ValueError, "dependency identity"):
            decaf.validate_inputs(inputs)

    def test_branch_name_cannot_replace_revision(self):
        inputs = json.loads(decaf.INPUTS.read_text())
        inputs["libraries"]["rust"]["candidate"] = "main"
        with self.assertRaisesRegex(ValueError, "full commit"):
            decaf.validate_inputs(inputs)

    def test_negative_control_requires_leak_diagnostic(self):
        for text in ("compile failed", "Program status is : unknown", "Program status is : insecure"):
            self.assertEqual(decaf.classify_analysis(text, "insecure", 0x1234)[0], "blocked")
        for kind in ("control flow", "memory access"):
            text = f"Instruction 0x42 has {kind} leak\nProgram status is : insecure"
            self.assertEqual(decaf.classify_analysis(text, "insecure", 0x1234)[0], "passed")
            self.assertEqual(decaf.classify_analysis(text, "secure", 0x1234)[0], "failed")

    def test_vacuous_and_incomplete_secure_results_are_blocked(self):
        secure = "Program status is : secure"
        self.assertEqual(decaf.classify_analysis(secure, "secure", 0x1234)[0], "blocked")
        text = secure + "\n[sse:result] Path 1 reached address 0x00001234"
        self.assertEqual(decaf.classify_analysis(text, "secure", 0x1234)[0], "passed")
        for extra in ("Exploration is incomplete", "unsupported instruction", secure):
            self.assertEqual(decaf.classify_analysis(text + "\n" + extra, "secure", 0x1234)[0], "blocked")

    def test_endpoint_must_match_positive_event_exactly(self):
        for event in ("[sse:result] Path 1 reached address 0xdead1234", "never reached address 0x1234"):
            self.assertEqual(decaf.classify_analysis("Program status is : secure\n" + event, "secure", 0x1234)[0], "blocked")

    def test_unsafe_arithmetic_dependency_cannot_be_assumed(self):
        # A trusted return replacing arkworks field arithmetic must be rejected,
        # even if the remaining caller trace would look constant-time.
        config = "starting from core\nreplace <ark_ff_multiply> by\n return\nend\nexplore all\n"
        with self.assertRaisesRegex(ValueError, "transitive dependencies"):
            decaf.validate_analysis_config(config)

    def test_undetected_negative_control_fails(self):
        self.assertEqual(decaf.classify_analysis("Program status is : secure", "insecure", 0x1234)[0], "failed")

    def test_blocker_report_never_certifies(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(decaf.formal, "WORK", Path(directory)):
                pilot = decaf.Pilot("leakage", "all")
                def unavailable(case):
                    raise decaf.Blocked("missing tool")
                pilot.check("example", "relational_analysis", unavailable)
                report = json.loads((pilot.reports / "report.json").read_text())
                self.assertEqual(report["status"], "blocked")
                self.assertFalse(report["full_certification"])
                self.assertEqual(report["checks"][0]["evidence_kind"], "relational_analysis")

    def test_mutation_requires_exact_operator(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "src/ark_curve/ops/projective.rs"
            source.parent.mkdir(parents=True)
            source.write_text("unrelated implementation")
            with self.assertRaisesRegex(decaf.Blocked, "no longer matches"):
                decaf.routing_mutation(root)
            self.assertEqual(source.read_text(), "unrelated implementation")


if __name__ == "__main__":
    unittest.main()
