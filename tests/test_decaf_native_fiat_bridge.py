import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import decaf_native_fiat_bridge as bridge


class NativeFiatBridgeTests(unittest.TestCase):
    def test_audit_binds_both_configured_moduli(self):
        source = bridge.audit_source({"fields": {"fq": "17", "fr": "19"}})
        self.assertIn("FiatMultiply.fq = (17)%Z := eq_refl.", source)
        self.assertIn("FiatMultiply.fr = (19)%Z := eq_refl.", source)
        self.assertEqual(source.count("Print Assumptions "), len(bridge.ROOTS))
        with self.assertRaises(ValueError):
            bridge.audit_source({"fields": {"fq": "17"}})
        with self.assertRaises(ValueError):
            bridge.audit_source({"fields": {"fq": "17). Axiom injected : False", "fr": "19"}})

    def test_closed_audit_is_exact_and_complete(self):
        output = "Closed under the global context\n" * len(bridge.ROOTS)
        bridge.validate_closed(output)
        for changed in (output + "Axioms: assumption : True\n", output.split("\n", 1)[1],
                        output + "Closed under the global context\n", ""):
            with self.subTest(changed=changed[-80:]), self.assertRaises(ValueError):
                bridge.validate_closed(changed)

    def test_native_receipt_requires_full_current_root_and_control_inventory(self):
        report = {"status": "passed", "completed": True, "full_certification": False,
                  "theorem_roots": list(bridge.native.ROOTS), "runner_sha256": "digest",
                  "matrix_sha256": "digest", "cases": {name: {
                      "input_hashes": {key: "digest" for key in ("Cargo.toml", "lib.rs", "fiat.rs")}}
                      for name in bridge.NATIVE_CASES}}
        changes = ({"status": "failed"}, {"completed": False}, {"full_certification": True},
                   {"theorem_roots": report["theorem_roots"][:-1]}, {"runner_sha256": "stale"},
                   {"matrix_sha256": "stale"}, {"cases": {"original": {}}})
        with patch.object(bridge.formal, "file_digest", return_value="digest"):
            for change in changes:
                with self.subTest(change=change), self.assertRaisesRegex(ValueError, "incomplete native"):
                    bridge.validate_native_receipt(dict(report, **change), Path("unused"))
            with self.assertRaisesRegex(ValueError, "negative-control stage"):
                bridge.validate_native_receipt(report, Path("unused"))

    def test_native_input_and_record_update_omissions_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            replay = root / "replay"
            records = root / "cache/record-update/src"
            paths = [replay / "original/support" / (name + ".vo")
                     for name in (*bridge.native.MODULES, "Audit")]
            paths += [(replay / "original/proofs/coq/extraction" / name).with_suffix(".vo")
                      for name in (*bridge.native.DERIVED_SOURCES, "Decaf_proof_slice_Fiat.v")]
            paths += [records / (name + ".vo") for name in ("RecordEta", "RecordSet")]
            for path in paths:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"artifact")
            cases = {name: {"input_hashes": {key: "digest" for key in ("Cargo.toml", "lib.rs", "fiat.rs")},
                            "rejection_stage": ("round-shape-inventory" if name == "wrong-late-carry" else
                                                "source-decomposition" if name == "wrong-suffix-connection" else "arithmetic-proof")}
                     for name in bridge.NATIVE_CASES}
            report = {"status": "passed", "completed": True, "full_certification": False,
                      "theorem_roots": list(bridge.native.ROOTS), "runner_sha256": "digest",
                      "matrix_sha256": "digest", "cases": cases,
                      "proof_hashes": dict.fromkeys(bridge.native.MODULES, "digest"),
                      "helper_hashes": dict.fromkeys((name for name in bridge.HELPERS if name != "decaf_field_proof.py"), "digest"),
                      "compiled_artifacts": {str(path.resolve()): "digest" for path in paths},
                      "record_update_sources": dict.fromkeys(("RecordEta", "RecordSet"), "digest")}
            with patch.object(bridge.formal, "CACHE", root / "cache"), \
                 patch.object(bridge.formal, "file_digest", return_value="digest"), \
                 patch.object(bridge.native, "validate_case_files"), \
                 patch.object(bridge.native, "validate_artifact_hashes"):
                bridge.validate_native_receipt(report, replay)
                for case in cases:
                    omitted = cases[case]["input_hashes"].pop("fiat.rs")
                    with self.subTest(case=case), self.assertRaisesRegex(ValueError, "input inventory"):
                        bridge.validate_native_receipt(report, replay)
                    cases[case]["input_hashes"]["fiat.rs"] = omitted
                for name in ("RecordEta", "RecordSet"):
                    path = str((records / (name + ".vo")).resolve())
                    digest = report["compiled_artifacts"].pop(path)
                    with self.subTest(name=name), self.assertRaisesRegex(ValueError, "omits an imported"):
                        bridge.validate_native_receipt(report, replay)
                    report["compiled_artifacts"][path] = digest
                    report["record_update_sources"].pop(name)
                    with self.assertRaisesRegex(ValueError, "RecordUpdate source"):
                        bridge.validate_native_receipt(report, replay)
                    report["record_update_sources"][name] = "digest"

    def test_failed_or_interrupted_refresh_invalidates_previous_success(self):
        for failure in (RuntimeError("cleanup failure"), KeyboardInterrupt()):
            with self.subTest(failure=type(failure).__name__), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                work = root / "decaf-native-fiat-bridge"
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


if __name__ == "__main__":
    unittest.main()
