#!/usr/bin/env python3
"""Replay exact Rust Fq / Fiat output correspondence in the supplied Core model."""
import json
import os
from pathlib import Path
import shutil

import formal
import decaf_field_proof as native
import decaf_fiat_proof as fiat
from decaf_inventory import atomic_json, MATRIX
from security import bounded_run

MODULE_ROOTS = {
    "MontgomeryBridge": ("congruence_witness", "congruence_from_witness",
                         "native_decoded_product", "cancel_decoding"),
    "FiatEndpoint": ("decode_correct", "fiat_decoded_product"),
    "FiatRepresentation": ("positional_value", "canonical_valid", "partition_words", "valid_canonical"),
    "NativeFiatEndpoint": ("raw_word_value", "raw_canonical", "raw_valid", "word_inverse",
                           "decoder_unit", "exact_fiat_multiplication"),
}
ROOTS = fiat.ROOTS + tuple(module + "." + name for module, names in MODULE_ROOTS.items() for name in names)
SOURCE_MODULES = ("FiatMultiply", *MODULE_ROOTS)
NATIVE_CASES = {"original", "wrong-modulus", "wrong-multiplication", "wrong-row-carry",
                "wrong-final-modulus", "wrong-final-selection", "wrong-late-carry", "wrong-suffix-connection"}
HELPERS = ("decaf_field_proof.py", "decaf_native_prefix.py", "decaf_fiat_proof.py", "decaf_fiat_build.py",
           "decaf_go_proof.py", "formal.py", "security.py", "decaf_inventory.py", "decaf_toolchain.py")


def validate_native_receipt(report, directory):
    if (report.get("status") != "passed" or report.get("completed") is not True or
            report.get("full_certification") is not False or
            report.get("theorem_roots") != list(native.ROOTS) or
            set(report.get("cases", {})) != NATIVE_CASES or
            report.get("runner_sha256") != formal.file_digest(formal.ROOT / "decaf_field_proof.py") or
            report.get("matrix_sha256") != formal.file_digest(MATRIX)):
        raise ValueError("missing, stale or incomplete native multiplication replay")
    for case, entry in report["cases"].items():
        if set(entry.get("input_hashes", {})) != {"Cargo.toml", "lib.rs", "fiat.rs"}:
            raise ValueError("native case input inventory is incomplete")
        expected = ("round-shape-inventory" if case == "wrong-late-carry" else
                    "source-decomposition" if case == "wrong-suffix-connection" else "arithmetic-proof")
        if case != "original" and entry.get("rejection_stage") != expected:
            raise ValueError("native negative-control stage is missing or incorrect")
    expected_proofs = {name: formal.file_digest(formal.ROOT / "decaf/proofs/rocq" / (name + ".v"))
                       for name in native.MODULES}
    if report.get("proof_hashes") != expected_proofs:
        raise ValueError("native handwritten proof identity changed")
    expected_helpers = {name: formal.file_digest(formal.ROOT / name) for name in HELPERS
                        if name != "decaf_field_proof.py"}
    if report.get("helper_hashes") != expected_helpers:
        raise ValueError("native replay helper identity changed")
    native.validate_case_files(directory, report["cases"], expected_proofs)
    native.validate_artifact_hashes(report.get("execution_artifacts", {}))
    native.validate_artifact_hashes(report.get("compiled_artifacts", {}))
    original = directory / "original"
    required = {str((original / "support" / (name + ".vo")).resolve(strict=True))
                for name in (*native.MODULES, "Audit")}
    required |= {str((original / "proofs/coq/extraction" / name).with_suffix(".vo").resolve(strict=True))
                 for name in (*native.DERIVED_SOURCES, "Decaf_proof_slice_Fiat.v")}
    records = formal.CACHE / "record-update/src"
    required |= {str((records / (name + ".vo")).resolve(strict=True)) for name in ("RecordEta", "RecordSet")}
    if not required <= report["compiled_artifacts"].keys():
        raise ValueError("native replay omits an imported proof artifact")
    if report.get("record_update_sources") != {
            name: formal.file_digest(records / (name + ".v")) for name in ("RecordEta", "RecordSet")}:
        raise ValueError("native RecordUpdate source inventory changed")


def validate_closed(text):
    if [line.strip() for line in text.splitlines() if line.strip()] != [
            "Closed under the global context"] * len(ROOTS):
        raise ValueError("endpoint assumptions are not closed")


def audit_source(config):
    if set(config["fields"]) != {"fq", "fr"}:
        raise ValueError("unexpected Fiat field inventory")
    text = "From Stdlib Require Import ZArith.\nRequire Import " + " ".join(SOURCE_MODULES) + ".\n"
    for field in ("fq", "fr"):
        modulus = int(config["fields"][field])
        text += f"Example {field}_identity : FiatMultiply.{field} = ({modulus})%Z := eq_refl.\n"
    return text + "\n".join("Print Assumptions " + root + "." for root in ROOTS) + "\n"


def main():
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-native-fiat-bridge"
        work.mkdir(parents=True, exist_ok=True)
        report_path = work / "report.json"
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "scope": "exact canonical Rust32 Fq multiplication output equality with the exact-options Fiat pipeline in the supplied Core semantics",
                  "kernel_reduction": "recursive Rocq kernel checking with bytecode reduction enabled; Fiat proof terms retain explicit Rocq VM/compiler trust",
                  "open_obligations": ["native execution and extraction semantics", "native overflow/panic safety and termination",
                                       "Rust Fr and Go arithmetic correspondence", "group, encoding, compiled traces and consumer closure"],
                  "theorem_roots": ROOTS, "commands": []}
        atomic_json(report_path, report)
        env = dict(os.environ, OPAMROOTISOK="1", COQPATH="", OCAMLPATH="",
                   OCAMLRUNPARAM="s=2M,o=20,O=50")

        def command(args, timeout=600):
            index = len(report["commands"])
            report["commands"].append(list(map(str, args)))
            atomic_json(report_path, report)
            logs = work / "logs"
            logs.mkdir(exist_ok=True)
            log = logs / f"{index:02}.log"
            native.validate_evidence_size(work)
            bounded_run(list(map(str, args)), work, env, log, work / "unused", logs, timeout)
            native.validate_evidence_size(work)
            return log.read_text()

        try:
            for child in work.iterdir():
                if child == report_path:
                    continue
                if child.is_dir() and not child.is_symlink():
                    shutil.rmtree(child)
                else:
                    child.unlink()
            native_dir = formal.WORK / "decaf-field-proof-replay"
            native_path = native_dir / "report.json"
            native_report = json.loads(native_path.read_text())
            validate_native_receipt(native_report, native_dir)
            config_path = formal.ROOT / "decaf/proofs/toolchain.json"
            config = json.loads(config_path.read_text())
            generation_path = formal.WORK / "decaf-fields/report.json"
            generation = json.loads(generation_path.read_text())
            fiat.validate_generation(config, generation, generation_path.parent)
            if formal.file_digest(native_dir / "original/fiat.rs") != formal.file_digest(
                    generation_path.parent / "rust/fq.rs"):
                raise ValueError("native multiplication source differs from the exact Fiat recipe output")
            build_path = formal.WORK / "decaf-fiat-build/report.json"
            build = json.loads(build_path.read_text())
            patch = formal.ROOT / "decaf/proofs/fiat-array-index.patch"
            fiat_source = fiat.validate_proof_build(config_path, build, patch)
            if (native_report["generation_receipt_sha256"] != formal.file_digest(generation_path) or
                    native_report["fiat_proof_build_receipt_sha256"] != formal.file_digest(build_path)):
                raise ValueError("native and Fiat proof dependencies differ")
            inputs = [Path(__file__), native_path, config_path, generation_path, build_path, MATRIX,
                      *(formal.ROOT / name for name in HELPERS),
                      *(formal.ROOT / "decaf/proofs/rocq" / (name + ".v") for name in SOURCE_MODULES)]
            report["input_hashes"] = {str(path.resolve(strict=True)): formal.file_digest(path) for path in inputs}
            report["native_replay_sha256"] = formal.file_digest(native_path)
            report["generation_receipt_sha256"] = formal.file_digest(generation_path)
            report["proof_build_receipt_sha256"] = formal.file_digest(build_path)
            rocq_env = ["opam", "exec", "--switch=decaf-fv", "--"]
            driver = Path(command([*rocq_env, "which", "rocq"]).strip()).resolve(strict=True)
            library = Path(command(["opam", "var", "lib", "--switch=decaf-fv"]).strip()).resolve(strict=True)
            worker = (library / "rocq-runtime/rocqworker").resolve(strict=True)
            checker = Path(command([*rocq_env, "which", "rocqchk"]).strip()).resolve(strict=True)
            report["execution_artifacts"] = {str(path): formal.file_digest(path) for path in (driver, worker, checker)}
            if (str(driver) != build["compiler"]["path"] or
                    formal.file_digest(driver) != build["compiler"]["sha256"] or
                    command([*rocq_env, driver, "-v"]) != build["rocq_version"] or
                    any(native_report["execution_artifacts"].get(path) != digest
                        for path, digest in report["execution_artifacts"].items())):
                raise ValueError("endpoint compiler differs from checked native/Fiat builds")
            original = native_dir / "original"
            flags = ["-Q", fiat_source / "src", "Crypto", "-Q", fiat_source / "coqprime/src/Coqprime", "Coqprime",
                     "-Q", fiat_source / "rupicola/bedrock2/deps/coqutil/src/coqutil", "coqutil",
                     "-Q", fiat_source / "rewriter/src/Rewriter", "Rewriter",
                     "-Q", formal.CACHE / "record-update/src", "RecordUpdate",
                     "-Q", original / "support", "Core", "-Q", original / "proofs/coq/extraction", "Slice",
                     "-Q", work, ""]
            compiler = [*rocq_env, worker, "--kind=compile", *flags,
                        "-I", fiat_source / "rewriter/src/Rewriter/Util/plugins"]
            report["compiled_artifacts"] = {}
            report["copied_sources"] = {}
            for name in SOURCE_MODULES:
                path = work / (name + ".v")
                shutil.copyfile(formal.ROOT / "decaf/proofs/rocq" / path.name, path)
                report["copied_sources"][str(path.resolve())] = formal.file_digest(path)
                command([*compiler, path])
                artifact = path.with_suffix(".vo").resolve(strict=True)
                report["compiled_artifacts"][str(artifact)] = formal.file_digest(artifact)
            audit = work / "BridgeAudit.v"
            audit.write_text(audit_source(config))
            report["copied_sources"][str(audit.resolve())] = formal.file_digest(audit)
            validate_closed(command([*compiler, audit]))
            artifact = audit.with_suffix(".vo").resolve(strict=True)
            report["compiled_artifacts"][str(artifact)] = formal.file_digest(artifact)
            for category in ("input_hashes", "execution_artifacts", "compiled_artifacts", "copied_sources"):
                native.validate_artifact_hashes(report[category])
            command([*rocq_env, checker, "-bytecode-compiler", "yes", "-silent", *flags,
                     *SOURCE_MODULES, "BridgeAudit"], timeout=1800)
            validate_native_receipt(native_report, native_dir)
            fiat.validate_proof_build(config_path, build, patch)
            fiat.validate_generation(config, generation, generation_path.parent)
            for category in ("input_hashes", "execution_artifacts", "compiled_artifacts", "copied_sources"):
                native.validate_artifact_hashes(report[category])
            report.update(status="passed", completed=True)
        except (Exception, KeyboardInterrupt) as error:
            report["detail"] = str(error) or "interrupted"
        finally:
            atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
