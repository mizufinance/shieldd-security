from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("gate-applicability.py")
SPEC = importlib.util.spec_from_file_location("gate_applicability", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GATE
SPEC.loader.exec_module(GATE)


class GateApplicabilityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        root = SCRIPT.parents[2]
        cls.snarkpack = GATE.load_declaration(
            root / "ci/gates/snarkpack-formal.json", "snarkpack-formal"
        )
        cls.soundness = GATE.load_declaration(
            root / "ci/gates/soundness-formal.json", "soundness-formal"
        )

    def test_formal_control_changes_select_both_pr_gates(self) -> None:
        path = "scripts/ci/gate-applicability.py"
        soundness = GATE.classify(
            self.soundness, "pull_request", [path], ()
        )
        snarkpack = GATE.classify(
            self.snarkpack, "pull_request", [path], ()
        )
        self.assertEqual(
            (soundness.status, soundness.tier), ("run", "policy")
        )
        self.assertEqual((snarkpack.status, snarkpack.tier), ("run", "static"))

    def test_unknown_pr_change_uses_each_fail_closed_tier(self) -> None:
        path = "future/formal-input"
        soundness = GATE.classify(
            self.soundness, "pull_request", [path], ()
        )
        snarkpack = GATE.classify(
            self.snarkpack, "pull_request", [path], ()
        )
        self.assertEqual((soundness.status, soundness.tier), ("run", "pr"))
        self.assertEqual(
            (snarkpack.status, snarkpack.tier), ("run", "extract-all")
        )

    def test_scheduled_work_is_always_full(self) -> None:
        for declaration in (self.soundness, self.snarkpack):
            decision = GATE.classify(declaration, "schedule", (), ())
            self.assertEqual((decision.status, decision.tier), ("run", "full"))

    def test_malformed_declaration_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "gate.json"
            path.write_text(json.dumps({"schema_version": 1}), encoding="utf-8")
            with self.assertRaises(GATE.ClassificationError):
                GATE.load_declaration(path, "fixture")


if __name__ == "__main__":
    unittest.main()
