import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import decaf_fr_fiat_bridge as bridge


class FrFiatBridgeTests(unittest.TestCase):
    def test_full_receipt_reconstruction_rejects_omissions_and_changes(self):
        # Fixture artifacts test receipt validation, not Rocq proof validity.
        # Extraction validation has separate actual-source and generator tests.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            work = root / "work"
            replay = work / "decaf-fr-field-proof"
            matrix = root / "decaf/obligations.json"
            proofs = root / "decaf/proofs/rocq"
            config = root / "decaf/proofs/toolchain.json"

            def write(path, text="fixture"):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
                return path

            write(matrix, "{}")
            write(config, '{"fields":{"fq":"17","fr":"19"}}')
            tool = write(root / "tool")
            artifacts = {str(tool.resolve()): bridge.formal.file_digest(tool)}
            fq_path = write(work / "decaf-field-proof-replay/report.json", json.dumps({
                "adopted_rust_source": {}, "execution_artifacts": artifacts}))
            source = "pub const fn fr_mul() {\n" + "\n".join(old for old, new in bridge.fr_native.MUTATIONS.values()) + "\n}\n"
            write(work / "decaf-fields/rust/fr.rs", source)
            write(work / "decaf-fields/report.json", "{}")
            write(work / "decaf-fiat-build/report.json", "{}")
            helpers = {"decaf_fr_native_prefix.py", "decaf_native_fiat_bridge.py", *bridge.fq_bridge.HELPERS}
            for name in {"decaf_fr_field_proof.py", *helpers}:
                write(root / name)
            for name in bridge.fr_native.MODULE_ROOTS:
                write(proofs / (name + ".v"), "proof source " + name)
            inputs = [root / "decaf_fr_field_proof.py", fq_path, config,
                      work / "decaf-fields/report.json", work / "decaf-fiat-build/report.json", matrix,
                      work / "decaf-fields/rust/fr.rs", *(root / name for name in helpers),
                      *(proofs / (name + ".v") for name in bridge.fr_native.MODULE_ROOTS)]
            report = {"status": "passed", "completed": True, "full_certification": False,
                      "theorem_roots": list(bridge.fr_native.ROOTS),
                      "native_parent_sha256": bridge.formal.file_digest(fq_path),
                      "adopted_rust_source": {}, "execution_artifacts": artifacts,
                      "input_hashes": {str(path.resolve()): bridge.formal.file_digest(path) for path in inputs},
                      "sources": {}, "compiled_artifacts": {}, "cases": {}}
            derived = {name + ".v": "checkpoint " + name for name in bridge.DERIVED_MODULES}
            derived["FrSuffixDefinition7.v"] = "let x7 := f_index arg1 ((7 : t_usize)) in\n"
            complete = ["Decaf_fr_slice_Fiat", "FrPrefix", "FrHelpers", "FrFirstReduction", "FrReductionBounds",
                        "FrRoundDefinition", "FrRound", "FrFinalDefinition", "FrFinal", "FrChain",
                        "FrAfterReductionDefinition", *(f"FrSuffixDefinition{i}" for i in range(1, 8)), "FrTail", "FrComplete"]
            for case in bridge.fr_native.CASES:
                case_dir = replay / case
                support = case_dir / "support"
                files = [write(case_dir / "fiat.rs", bridge.fr_native.mutate_source(source, case)),
                         write(case_dir / "lib.rs", bridge.fr_native.witness_source(19)),
                         write(case_dir / "Cargo.toml", '[package]\nname="decaf_fr_slice"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')]
                extracted = write(case_dir / "proofs/coq/extraction/Decaf_fr_slice_Fiat.v", "extraction")
                files.append(extracted)
                case_derived = bridge.fr_native.suffix_mutation(derived) if case == "wrong-suffix-connection" else derived
                files.extend(write(support / name, text) for name, text in case_derived.items())
                files.extend(write(support / (name + ".v"), (proofs / (name + ".v")).read_text()) for name in bridge.fr_native.MODULE_ROOTS)
                count = (3 if case in ("wrong-coefficient", "wrong-discarded-carry") else
                         8 if case == "wrong-final-selection" else 18 if case == "wrong-suffix-connection" else 20)
                entry = {"source_sha256": bridge.formal.file_digest(case_dir / "fiat.rs"), "compiled_modules": complete[:count]}
                if case != "original":
                    entry["rejected_at"] = "FrFirstReduction" if count == 3 else "FrFinal" if count == 8 else "FrTail"
                    entry["rejection_stage"] = ("discarded-carry-propagation-guard" if case == "wrong-discarded-carry" else
                                                "source-decomposition" if case == "wrong-suffix-connection" else "arithmetic-proof")
                else:
                    audit = ("From Stdlib Require Import ZArith.\nRequire Import " + " ".join(bridge.fr_native.MODULE_ROOTS) + ".\n"
                             + 'Example fr_identity : FrFirstReduction.fr_modulus = (19)%Z := eq_refl.\n'
                             + "\n".join("Print Assumptions " + name + "." for name in bridge.fr_native.ROOTS) + "\n")
                    files.append(write(support / "FrAudit.v", audit))
                compiled = [write(extracted.with_suffix(".vo"))]
                compiled.extend(write(support / (name + ".vo")) for name in complete[1:count])
                if case == "original":
                    compiled.append(write(support / "FrAudit.vo"))
                report["cases"][case] = entry
                report["sources"].update({str(path.resolve()): bridge.formal.file_digest(path) for path in files})
                report["compiled_artifacts"].update({str(path.resolve()): bridge.formal.file_digest(path) for path in compiled})
            with patch.object(bridge.formal, "ROOT", root), patch.object(bridge.formal, "WORK", work), \
                 patch.object(bridge, "MATRIX", matrix), patch.object(bridge.fq_bridge, "validate_native_receipt"), \
                 patch.object(bridge.fr_native, "validate_extraction"), \
                 patch.object(bridge, "multiplication_checkpoints", return_value=derived):
                bridge.validate_native_receipt(report, replay)
                for category, path in (("sources", replay / "original/support/FrTail.v"),
                                       ("compiled_artifacts", replay / "original/support/FrTail.vo")):
                    key = str(path.resolve())
                    saved = report[category].pop(key)
                    with self.subTest(category=category), self.assertRaisesRegex(ValueError, "inventory is incomplete"):
                        bridge.validate_native_receipt(report, replay)
                    report[category][key] = saved
                for path, reason in ((replay / "original/support/FrSuffixDefinition7.v", "checkpoint source"),
                                     (replay / "original/lib.rs", "native witnesses"),
                                     (replay / "original/support/FrAudit.v", "modulus audit")):
                    saved = path.read_text()
                    path.write_text(saved + "changed")
                    with self.subTest(path=path), self.assertRaisesRegex(ValueError, reason):
                        bridge.validate_native_receipt(report, replay)
                    path.write_text(saved)

    def test_exact_moduli_and_complete_endpoint_audit(self):
        source = bridge.audit_source({"fields": {"fq": "17", "fr": "19"}})
        self.assertIn("FiatMultiply.fr = (19)%Z := eq_refl.", source)
        self.assertIn("Print Assumptions FrNativeFiatEndpoint.exact_fiat_multiplication.", source)
        self.assertEqual(source.count("Print Assumptions "), 24)
        closed = "Closed under the global context\n" * 24
        bridge.validate_closed(closed)
        for changed in (closed.split("\n", 1)[1], closed + "Axioms: assumed\n", ""):
            with self.assertRaises(ValueError):
                bridge.validate_closed(changed)

    def test_missing_native_closure_cannot_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            parent = root / "decaf-field-proof-replay/report.json"
            parent.parent.mkdir()
            parent.write_text(json.dumps({"adopted_rust_source": {}, "execution_artifacts": {}}))
            report = {"status": "passed", "completed": True, "full_certification": False,
                      "theorem_roots": list(bridge.fr_native.ROOTS), "native_parent_sha256": "digest",
                      "adopted_rust_source": {}, "execution_artifacts": {},
                      "cases": dict.fromkeys(bridge.NATIVE_CASES, {})}
            changes = ({"status": "failed"}, {"completed": False}, {"full_certification": True},
                       {"theorem_roots": report["theorem_roots"][:-1]}, {"native_parent_sha256": "stale"},
                       {"cases": {"original": {}}}, {"execution_artifacts": {"unexpected": "tool"}})
            with patch.object(bridge.formal, "WORK", root), \
                 patch.object(bridge.formal, "file_digest", return_value="digest"), \
                 patch.object(bridge.fq_bridge, "validate_native_receipt"):
                for change in changes:
                    with self.subTest(change=change), self.assertRaisesRegex(ValueError, "incomplete Fr native"):
                        bridge.validate_native_receipt(dict(report, **change), root / "unused")

    def test_interruption_cannot_retain_old_success(self):
        for failure in (RuntimeError("cleanup failed"), KeyboardInterrupt()):
            with self.subTest(failure=type(failure).__name__), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                work = root / "decaf-fr-fiat-bridge"
                (work / "old").mkdir(parents=True)
                report = work / "report.json"
                report.write_text('{"status":"passed","completed":true,"full_certification":true}')
                with patch.object(bridge.formal, "WORK", root), \
                     patch.object(bridge.formal, "exclusive_lock", contextlib.nullcontext), \
                     patch.object(bridge.shutil, "rmtree", side_effect=failure), \
                     contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(bridge.main(), 1)
                state = json.loads(report.read_text())
                self.assertEqual(state["status"], "failed")
                self.assertFalse(state["completed"])
                self.assertFalse(state["full_certification"])
