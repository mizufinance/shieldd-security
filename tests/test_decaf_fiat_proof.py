import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import formal
from decaf_fiat_proof import generation_options, validate_generation, validate_proof_build
from decaf_toolchain import native_artifact


class FiatRecipeTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.config = json.loads((formal.ROOT / "decaf/proofs/toolchain.json").read_text())
        host = patch("decaf_toolchain.native_host", return_value="x86_64-unknown-linux-gnu")
        host.start()
        self.addCleanup(host.stop)
        native = native_artifact(self.config, "fiat")
        self.receipt = dict(status="generated", completed=True,
                            fiat_revision=self.config["fiat"]["revision"], native_host=native["host"],
                            generator_sha256=native["binary_sha256"],
                            generator_patch_sha256=native["printer_patch_sha256"], outputs=[])
        for language, extension in (("rust", "rs"), ("go", "go")):
            (self.root / language).mkdir()
            for field in ("fq", "fr"):
                path = f"{language}/{field}.{extension}"
                (self.root / path).write_bytes(path.encode())
                self.receipt["outputs"].append(dict(path=path, sha256=formal.file_digest(self.root / path), command=[
                    ".cache/fiat-crypto/src/ExtractionOCaml/fiat_crypto", "word-by-word-montgomery",
                    *generation_options(language), "--output", ".work/decaf-fields/" + path,
                    field, str(self.config["representations"][language]), self.config["fields"][field]]))

    def test_complete_recipe_is_accepted(self):
        validate_generation(self.config, self.receipt, self.root)

    def test_each_command_argument_is_bound(self):
        for output in range(4):
            for index in range(len(self.receipt["outputs"][output]["command"])):
                with self.subTest(output=output, index=index):
                    changed = copy.deepcopy(self.receipt)
                    changed["outputs"][output]["command"][index] += "-mutated"
                    with self.assertRaises(ValueError):
                        validate_generation(self.config, changed, self.root)

    def test_omitted_or_extra_generation_flag_is_rejected(self):
        for change in (lambda args: args.pop(4), lambda args: args.insert(4, "--no-select")):
            changed = copy.deepcopy(self.receipt)
            change(changed["outputs"][2]["command"])
            with self.assertRaises(ValueError):
                validate_generation(self.config, changed, self.root)

    def test_missing_duplicate_and_unknown_outputs_are_rejected(self):
        for paths in ((0, 1, 2), (0, 1, 2, 2)):
            changed = copy.deepcopy(self.receipt)
            changed["outputs"] = [changed["outputs"][i] for i in paths]
            with self.assertRaises(ValueError):
                validate_generation(self.config, changed, self.root)
        self.receipt["outputs"][0]["path"] = "../fq.rs"
        with self.assertRaises(ValueError):
            validate_generation(self.config, self.receipt, self.root)

    def test_changed_source_bytes_are_rejected(self):
        (self.root / "go/fr.go").write_bytes(b"changed arithmetic")
        with self.assertRaisesRegex(ValueError, "bytes"):
            validate_generation(self.config, self.receipt, self.root)

    def test_stale_identity_or_incomplete_generation_is_rejected(self):
        for key, value in (("status", "passed"), ("completed", False), ("fiat_revision", "0" * 40),
                           ("native_host", "aarch64-apple-darwin"), ("generator_sha256", "0" * 64),
                           ("generator_patch_sha256", "0" * 64)):
            with self.subTest(key=key):
                changed = dict(self.receipt, **{key: value})
                with self.assertRaises(ValueError):
                    validate_generation(self.config, changed, self.root)

    def proof_build(self):
        config_path = self.root / "config.json"
        config_path.write_text(json.dumps(self.config))
        patch_path = formal.ROOT / "decaf/proofs/fiat-array-index.patch"
        source = self.root / "source"
        source.mkdir()
        artifacts = {}
        for relative in ("src/PushButtonSynthesis/WordByWordMontgomery.vo", "src/Stringification/Language.vo"):
            path = source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(relative.encode())
            artifacts[relative] = formal.file_digest(path)
        input_path = source / "input.v"
        input_path.write_text("source")
        receipt = dict(status="passed", completed=True, source_root=str(source),
                       sources=[dict(revision=self.config["fiat"]["revision"])],
                       source_files={"input.v": formal.file_digest(input_path)}, artifacts=artifacts,
                       toolchain_sha256=formal.file_digest(config_path),
                       runner_sha256=formal.file_digest(formal.ROOT / "decaf_fiat_build.py"),
                       patch_sha256=formal.file_digest(patch_path))
        return config_path, receipt, patch_path, source

    def test_proof_build_artifact_and_source_bytes_are_bound(self):
        config, receipt, patch_path, source = self.proof_build()
        self.assertEqual(validate_proof_build(config, receipt, patch_path), source.resolve())
        for name in ("input.v", "src/Stringification/Language.vo"):
            path = source / name
            original = path.read_bytes()
            path.write_bytes(b"mutated")
            with self.assertRaisesRegex(ValueError, "changed"):
                validate_proof_build(config, receipt, patch_path)
            path.write_bytes(original)
        (source / "extra.vo").write_bytes(b"unrecorded import")
        with self.assertRaisesRegex(ValueError, "unrecorded"):
            validate_proof_build(config, receipt, patch_path)

    def test_changed_patch_cannot_be_authorized_by_a_matching_receipt(self):
        config, receipt, patch_path, source = self.proof_build()
        changed_patch = self.root / "changed.patch"
        changed_patch.write_bytes(patch_path.read_bytes() + b"\nchanged\n")
        receipt["patch_sha256"] = formal.file_digest(changed_patch)
        with self.assertRaisesRegex(ValueError, "patch bytes"):
            validate_proof_build(config, receipt, changed_patch)

    def test_incomplete_or_stale_build_provenance_is_rejected(self):
        config, receipt, patch_path, source = self.proof_build()
        for key, value in (("status", "blocked"), ("completed", False), ("runner_sha256", "0" * 64),
                           ("toolchain_sha256", "0" * 64), ("sources", []), ("artifacts", {})):
            with self.subTest(key=key), self.assertRaises(ValueError):
                validate_proof_build(config, dict(receipt, **{key: value}), patch_path)


if __name__ == "__main__":
    unittest.main()
