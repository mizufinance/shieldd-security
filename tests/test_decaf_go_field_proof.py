import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import formal
from decaf_fiat_proof import generation_options
from decaf_go_field_proof import (
    early_write_mutation, modulus_mutation, validate_field_rejection, validate_generation, validate_native_rejection)
import decaf_go_field_proof as replay
from contextlib import nullcontext


class GoFieldProofGateTests(unittest.TestCase):
    def test_go_source_inventory_rejects_added_removed_and_changed_files(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "src/math/bits/bits.go"
            include = root / "pkg/include/textflag.h"
            for path in (source, include):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("original\n")
            expected = replay.go_source_inventory(root)
            replay.validate_go_sources(root, expected)
            for directory in (source.parent, include.parent):
                added = directory / "added.go"
                added.write_text("new input\n")
                with self.assertRaisesRegex(ValueError, "inventory changed"):
                    replay.validate_go_sources(root, expected)
                added.unlink()
            source.unlink()
            with self.assertRaisesRegex(ValueError, "inventory changed"):
                replay.validate_go_sources(root, expected)
            source.write_text("changed\n")
            with self.assertRaisesRegex(ValueError, "inventory changed"):
                replay.validate_go_sources(root, expected)
            source.write_text("original\n")
            replay.validate_go_sources(root, expected)

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
                patch("decaf_fiat_proof.native_artifact", return_value=build):
            directory = Path(temporary)
            (directory / "go").mkdir()
            (directory / "rust").mkdir()
            receipt = {"status": "generated", "completed": True, "native_host": build["host"],
                       "fiat_revision": config["fiat"]["revision"],
                       "generator_sha256": build["binary_sha256"],
                       "generator_patch_sha256": build["printer_patch_sha256"], "outputs": []}
            for language, extension in (("rust", "rs"), ("go", "go")):
                for field in ("fq", "fr"):
                    path = f"{language}/{field}.{extension}"
                    source = directory / path
                    source.write_text("fixture source\n")
                    receipt["outputs"].append({"path": path, "sha256": formal.file_digest(source), "command": [
                        ".cache/fiat-crypto/src/ExtractionOCaml/fiat_crypto", "word-by-word-montgomery",
                        *generation_options(language), "--output", ".work/decaf-fields/" + path,
                        field, str(config["representations"][language]), config["fields"][field]]})
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
            changed["outputs"][0]["command"][-2] = "64"
            with self.assertRaises(ValueError):
                validate_generation(config, changed, directory)
            changed = copy.deepcopy(receipt)
            changed["outputs"][2]["command"].remove("--no-wide-int")
            with self.assertRaises(ValueError):
                validate_generation(config, changed, directory)
            (directory / "go/fr.go").write_text("package changed\n")
            with self.assertRaises(ValueError):
                validate_generation(config, receipt, directory)

    def test_rejection_requires_single_exact_absolute_error_site(self):
        path = Path(tempfile.gettempdir()).resolve() / "GoFieldAdd.v"
        proof = "split; [lia|apply Z.mod_unique with (q := 1); lia]."
        output = f'File "{path}", line 1, characters 0-1:\nError: Tactic failure:  Cannot find witness.'
        validate_field_rejection(output, proof, "fq", path)
        for invalid in (output + "\n" + output,
                        output.replace(str(path), str(path.parent / "other/GoFieldAdd.v")),
                        'Error: earlier failure\n' + output):
            with self.assertRaises(ValueError):
                validate_field_rejection(invalid, proof, "fq", path)
        with self.assertRaises(ValueError):
            validate_field_rejection(output, proof, "fq", Path("GoFieldAdd.v"))

    def test_early_write_requires_offset_witness_and_exact_execution_stage(self):
        proof = "Proof.\narray_steps. wp_func_call.\narray_steps. wp_func_call.\n"
        for field, module in (("fq", "GoFieldAdd"), ("fr", "GoFrFieldAdd")):
            source = f"func {field.capitalize()}Add(out1 *[4]uint64, arg1 *[4]uint64, arg2 *[4]uint64) {{\n}}"
            mutated = early_write_mutation(source, field)
            self.assertIn("out1[0] = arg1[0]", mutated)
            with self.assertRaises(ValueError):
                early_write_mutation(mutated, field)
            path = Path(tempfile.gettempdir()).resolve() / (module + ".v")
            output = (f'File "{path}", line 2, characters 0-1:\nError: The LHS of func_unfold\n'
                      '    (# (functions _ _))\n\ndoes not match any subterm of the goal\n')
            validate_field_rejection(output, proof, field, path, "early-write")
            for invalid in (output.replace("line 2", "line 3"),
                            output.replace("The LHS of func_unfold", "inconsistent assumptions over library")):
                with self.assertRaises(ValueError):
                    validate_field_rejection(invalid, proof, field, path, "early-write")
            native = f"--- FAIL: TestFieldOffsetWindows (0.00s)\n{field} offsets out=1 p=0 q=0 pattern=2: wrong frame"
            validate_native_rejection(native, field, "early-write")
            with self.assertRaises(ValueError):
                validate_native_rejection(native.replace("TestFieldOffsetWindows", "TestOther"), field, "early-write")

    def test_interrupted_refresh_invalidates_old_success(self):
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            directory = work / "decaf-go-field-proof-replay"
            directory.mkdir()
            path = directory / "report.json"
            path.write_text('{"status":"passed","completed":true}')
            with patch.object(formal, "WORK", work), patch.object(formal, "exclusive_lock", return_value=nullcontext()), \
                    patch("decaf_go_field_proof.tempfile.mkdtemp", side_effect=KeyboardInterrupt):
                self.assertEqual(replay.main(), 1)
            report = json.loads(path.read_text())
            self.assertEqual(report["status"], "failed")
            self.assertFalse(report["completed"])
            self.assertFalse(report["full_certification"])
