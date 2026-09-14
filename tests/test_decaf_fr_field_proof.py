import unittest
from pathlib import Path
import tempfile
from unittest.mock import patch

import decaf_fr_field_proof as proof


class FrReplayTests(unittest.TestCase):
    def test_changed_extraction_dispatch_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            cargo = Path(directory) / "cargo"
            other = Path(directory) / "other-cargo"
            cargo.touch()
            other.touch()
            hax = {"cargo-hax": Path(directory) / "cargo-hax"}
            base = {"hax_tool_paths": {key: str(value) for key, value in hax.items()},
                    "rust_tool_paths": {"extraction": {"cargo": str(cargo.resolve())}}}
            with patch.object(proof.native, "hax_tool_paths", return_value=hax):
                proof.validate_dispatch(lambda args: str(cargo), base)
                with self.assertRaisesRegex(ValueError, "Cargo dispatch"):
                    proof.validate_dispatch(lambda args: str(other), base)
            with patch.object(proof.native, "hax_tool_paths", return_value={}):
                with self.assertRaisesRegex(ValueError, "hax dispatch"):
                    proof.validate_dispatch(lambda args: str(cargo), base)

    def test_source_mutations_are_confined_to_multiplication(self):
        for case, (old, new) in proof.MUTATIONS.items():
            source = "pub const fn fr_mul() {\n" + old + "\n}\n" + "pub const fn fr_square() {\n" + old + "\n}\n"
            with self.subTest(case=case):
                changed = proof.mutate_source(source, case)
                self.assertEqual(changed.count(old), 1)
                self.assertEqual(changed.count(new), 1)
                self.assertTrue(changed.endswith("pub const fn fr_square() {\n" + old + "\n}\n"))
                with self.assertRaises(ValueError):
                    proof.mutate_source(changed, case)

    def test_unknown_control_fails(self):
        with self.assertRaises(ValueError):
            proof.mutate_source("", "unsupported-case")

    def test_suffix_fault_changes_only_final_digit_input(self):
        sources = {"FrSuffixDefinition7.v": "let x7 := f_index arg1 ((7 : t_usize)) in\n",
                   "FrFinalDefinition.v": "unchanged"}
        changed = proof.suffix_mutation(sources)
        self.assertEqual(changed["FrFinalDefinition.v"], sources["FrFinalDefinition.v"])
        self.assertIn("((6 :", changed["FrSuffixDefinition7.v"])
        self.assertIn("((7 :", sources["FrSuffixDefinition7.v"])
        with self.assertRaises(ValueError):
            proof.suffix_mutation(changed)

    def test_incomplete_or_nonclosed_audits_fail(self):
        closed = "Closed under the global context\n" * 39
        proof.validate_closed(closed)
        for changed in (closed.removeprefix("Closed under the global context\n"),
                        closed + "Axioms:\n", "", closed.replace("Closed", "Assumed", 1)):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                proof.validate_closed(changed)

    def test_reduction_control_rejects_unrelated_failures(self):
        error = 'File "FrFirstReduction.v", line 31, characters 2-363:\nError: No matching clauses for match.\n'
        proof.validate_rejection(error, "FrFirstReduction.v", "wrong-coefficient")
        for changed in (error.replace("FrFirstReduction.v", "Core.v"),
                        error.replace("No matching clauses for match", "Syntax error"),
                        error + "Error: interrupted\n", "timeout", ""):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                proof.validate_rejection(changed, "FrFirstReduction.v", "wrong-coefficient")

    def test_actual_absolute_control_paths(self):
        for case, module, reason in (("wrong-final-selection", "FrFinal", "Cannot find witness."),
                                     ("wrong-suffix-connection", "FrTail", "round tails differ syntactically")):
            path = "/proof/work/" + case + "/" + module + ".v"
            error = f'File "{path}", line 17, characters 2-14:\nError: Tactic failure: {reason}.\n'
            error = error.replace("witness..", "witness.")
            proof.validate_rejection(error, path, case)
            with self.assertRaises(ValueError):
                proof.validate_rejection(error, module + ".v", case)

    def test_carry_guard_is_distinguished_from_arithmetic_failure(self):
        path = "/proof/wrong-discarded-carry/FrFirstReduction.v"
        error = f'File "{path}", line 65, characters 2-211:\nError: Tactic failure: Fr discarded carry is not propagated.\n'
        proof.validate_rejection(error, path, "wrong-discarded-carry")
        with self.assertRaises(ValueError):
            proof.validate_rejection(error, path, "wrong-coefficient")
        with self.assertRaises(ValueError):
            proof.validate_rejection(error.replace("Tactic failure: Fr discarded carry is not propagated", "No matching clauses for match"), path, "wrong-discarded-carry")
