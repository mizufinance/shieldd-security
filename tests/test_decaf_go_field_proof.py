import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import formal
from decaf_go_field_proof import (
    modulus_mutation, validate_field_rejection, validate_generation, validate_native_rejection)


class GoFieldProofGateTests(unittest.TestCase):
    def test_fr_mutation_and_rejection_are_independent_of_fq(self):
        source = "func FrAdd() {\n x := 0xb95aee9ac33fd9ff\n}\nfunc FrSub() {\n x := 0xb95aee9ac33fd9ff\n}\n"
        mutated = modulus_mutation(source, "fr")
        self.assertIn("func FrAdd() {\n x := 0xb95aee9ac33fda00", mutated)
        self.assertEqual(mutated.split("func FrSub", 1)[1], source.split("func FrSub", 1)[1])
        with self.assertRaises(ValueError):
            modulus_mutation(mutated, "fr")
        proof = "split; [lia|apply Z.mod_unique with (q := 1); lia]."
        diagnostic = 'File "GoFrFieldAdd.v", line 1, characters 1-10:\nError: Tactic failure:  Cannot find witness.'
        native = "--- FAIL: TestFrBoundary (0.00s)\nfr boundary witness: [1]"
        validate_field_rejection(diagnostic, proof, "fr")
        validate_native_rejection(native, "fr")
        with self.assertRaises(ValueError):
            validate_field_rejection(diagnostic, proof, "fq")
        with self.assertRaises(ValueError):
            validate_field_rejection(diagnostic.replace("GoFrFieldAdd", "GoFieldAdd"), proof, "fr")
        with self.assertRaises(ValueError):
            validate_native_rejection(native, "fq")
        with self.assertRaises(ValueError):
            validate_native_rejection(native.replace("Fr", "Fq").replace("fr", "fq"), "fr")

    def test_native_rejection_requires_the_named_arithmetic_witness(self):
        validate_native_rejection("--- FAIL: TestFqBoundary (0.00s)\nfield_test.go:7: fq boundary witness: [1]")
        for output in ("fq boundary witness:", "--- FAIL: TestFqBoundary (0.00s)\nbuild failed",
                       "--- FAIL: TestOther (0.00s)\nfq boundary witness:"):
            with self.assertRaises(ValueError):
                validate_native_rejection(output)

    def test_mutation_changes_only_the_addition_modulus(self):
        source = "func FqAdd() {\n x := 0xa11800000000001\n}\nfunc FqSub() {\n x := 0xa11800000000001\n}\n"
        mutated = modulus_mutation(source)
        self.assertIn("func FqAdd() {\n x := 0xa11800000000002", mutated)
        self.assertEqual(mutated.split("func FqSub", 1)[1], source.split("func FqSub", 1)[1])
        with self.assertRaises(ValueError):
            modulus_mutation(mutated)

    def test_infrastructure_and_execution_errors_cannot_pass_as_arithmetic_rejection(self):
        proof = "Lemma add_correct : True.\nProof.\n split; [lia|apply Z.mod_unique with (q := 1); lia].\nQed."
        valid = 'File "GoFieldAdd.v", line 3, characters 12-15:\nError: Tactic failure:  Cannot find witness.'
        validate_field_rejection(valid, proof)
        for invalid in (valid.replace("line 3", "line 2"),
                        valid.replace("GoFieldAdd.v", "GoSelect.v"),
                        valid.replace("Tactic failure:  Cannot find witness.", "Cannot find library fiat."),
                        "Killed", "Timeout"):
            with self.assertRaises(ValueError):
                validate_field_rejection(invalid, proof)

    def test_receipt_drift_is_rejected_before_extraction(self):
        config = json.loads((Path(__file__).resolve().parents[1] / "decaf/proofs/toolchain.json").read_text())
        build = dict(config["native_builds"]["x86_64-unknown-linux-gnu"]["fiat"],
                     host="x86_64-unknown-linux-gnu")
        with tempfile.TemporaryDirectory() as temporary, \
                patch("decaf_go_field_proof.native_artifact", return_value=build):
            directory = Path(temporary)
            (directory / "go").mkdir()
            receipt = {"status": "generated", "completed": True, "native_host": build["host"],
                       "fiat_revision": config["fiat"]["revision"],
                       "generator_sha256": build["binary_sha256"],
                       "generator_patch_sha256": build["printer_patch_sha256"], "outputs": []}
            for field in ("fq", "fr"):
                source = directory / "go" / f"{field}.go"
                source.write_text("package fiat\n")
                receipt["outputs"].append({"path": f"go/{field}.go", "sha256": formal.file_digest(source),
                                            "command": [field, "64", config["fields"][field]]})
            validate_generation(config, receipt, directory)
            for key, value in (("completed", False), ("native_host", "aarch64-apple-darwin"),
                               ("generator_sha256", "0" * 64), ("generator_patch_sha256", "0" * 64)):
                changed = copy.deepcopy(receipt)
                changed[key] = value
                with self.assertRaises(ValueError):
                    validate_generation(config, changed, directory)
            for outputs in (receipt["outputs"][:1], receipt["outputs"] + receipt["outputs"][:1]):
                with self.assertRaises(ValueError):
                    validate_generation(config, receipt | {"outputs": outputs}, directory)
            changed = copy.deepcopy(receipt)
            changed["outputs"][0]["command"][-2] = "32"
            with self.assertRaises(ValueError):
                validate_generation(config, changed, directory)
            (directory / "go/fr.go").write_text("package changed\n")
            with self.assertRaises(ValueError):
                validate_generation(config, receipt, directory)
