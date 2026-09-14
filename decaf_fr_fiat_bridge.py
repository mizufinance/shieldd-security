#!/usr/bin/env python3
"""Replay exact Rust Fr / Fiat output correspondence in the supplied Core model."""
import json
import os
from pathlib import Path
import shutil

import formal
import decaf_field_proof as native
import decaf_fr_field_proof as fr_native
import decaf_native_fiat_bridge as fq_bridge
from decaf_fr_native_prefix import multiplication_checkpoints, DERIVED_MODULES
import decaf_fiat_proof as fiat
from decaf_inventory import atomic_json, MATRIX
from security import bounded_run

MODULE_ROOTS = {
    "MontgomeryBridge": ("congruence_witness", "congruence_from_witness",
                         "native_decoded_product", "cancel_decoding"),
    "FrFiatEndpoint": ("decode_correct", "fiat_decoded_product"),
    "FrFiatRepresentation": ("positional_value", "canonical_valid", "partition_words", "valid_canonical"),
    "FrNativeFiatEndpoint": ("raw_word_value", "raw_canonical", "raw_valid", "word_inverse",
                           "decoder_unit", "exact_fiat_multiplication"),
}
ROOTS = fiat.ROOTS + tuple(module + "." + name for module, names in MODULE_ROOTS.items() for name in names)
SOURCE_MODULES = ("FiatMultiply", *MODULE_ROOTS)
NATIVE_CASES = set(fr_native.CASES)
HELPERS = (*fq_bridge.HELPERS, "decaf_native_fiat_bridge.py", "decaf_fr_field_proof.py", "decaf_fr_native_prefix.py")


def validate_native_receipt(report, directory):
    fq_directory = formal.WORK / "decaf-field-proof-replay"
    fq_path = fq_directory / "report.json"
    fq_report = json.loads(fq_path.read_text())
    fq_bridge.validate_native_receipt(fq_report, fq_directory)
    if (report.get("status") != "passed" or report.get("completed") is not True or
            report.get("full_certification") is not False or
            report.get("theorem_roots") != list(fr_native.ROOTS) or
            set(report.get("cases", {})) != NATIVE_CASES or
            report.get("native_parent_sha256") != formal.file_digest(fq_path) or
            report.get("adopted_rust_source") != fq_report["adopted_rust_source"] or
            report.get("execution_artifacts") != fq_report["execution_artifacts"]):
        raise ValueError("missing, stale or incomplete Fr native multiplication replay")
    generated = formal.WORK / "decaf-fields"
    config_path = formal.ROOT / "decaf/proofs/toolchain.json"
    config = json.loads(config_path.read_text())
    fr_helpers = {"decaf_fr_native_prefix.py", "decaf_native_fiat_bridge.py", *fq_bridge.HELPERS}
    inputs = [formal.ROOT / "decaf_fr_field_proof.py", fq_path, config_path,
              generated / "report.json", formal.WORK / "decaf-fiat-build/report.json", MATRIX,
              generated / "rust/fr.rs", *(formal.ROOT / name for name in fr_helpers),
              *(formal.ROOT / "decaf/proofs/rocq" / (name + ".v") for name in fr_native.MODULE_ROOTS)]
    expected_inputs = {str(path.resolve(strict=True)): formal.file_digest(path) for path in inputs}
    if report.get("input_hashes") != expected_inputs:
        raise ValueError("Fr proof input inventory is incomplete or stale")
    source = (generated / "rust/fr.rs").read_text()
    required_sources, required_artifacts = set(), set()
    for case in fr_native.CASES:
        entry = report["cases"][case]
        case_directory = directory / case
        support = case_directory / "support"
        changed = fr_native.mutate_source(source, case)
        if (case_directory / "fiat.rs").read_text() != changed:
            raise ValueError("Fr case source mutation changed")
        if entry.get("source_sha256") != formal.file_digest(case_directory / "fiat.rs"):
            raise ValueError("Fr case source identity changed")
        if (case_directory / "lib.rs").read_text() != fr_native.witness_source(int(config["fields"]["fr"])):
            raise ValueError("Fr native witnesses changed")
        manifest = '[package]\nname="decaf_fr_slice"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n'
        if (case_directory / "Cargo.toml").read_text() != manifest:
            raise ValueError("Fr extraction package or dependency configuration changed")
        extracted = case_directory / "proofs/coq/extraction/Decaf_fr_slice_Fiat.v"
        fr_native.validate_extraction(extracted.read_text())
        derived = multiplication_checkpoints(extracted.read_text())
        if case == "wrong-suffix-connection":
            derived = fr_native.suffix_mutation(derived)
        for name, text in derived.items():
            if (support / name).read_text() != text:
                raise ValueError("Fr checkpoint source changed")
        files = [case_directory / name for name in ("Cargo.toml", "lib.rs", "fiat.rs")]
        files += [support / name for name in derived]
        files += [extracted]
        for name in fr_native.MODULE_ROOTS:
            path = support / (name + ".v")
            if formal.file_digest(path) != formal.file_digest(formal.ROOT / "decaf/proofs/rocq" / path.name):
                raise ValueError("Fr handwritten proof copy changed")
            files.append(path)
        reject = ("FrFirstReduction" if case in ("wrong-coefficient", "wrong-discarded-carry") else
                  "FrFinal" if case == "wrong-final-selection" else
                  "FrTail" if case == "wrong-suffix-connection" else None)
        completed = ["Decaf_fr_slice_Fiat", "FrPrefix"]
        for module in fr_native.MODULE_ROOTS:
            completed.extend({"FrRound": ("FrRoundDefinition",), "FrFinal": ("FrFinalDefinition",),
                              "FrTail": ("FrAfterReductionDefinition", *(f"FrSuffixDefinition{i}" for i in range(1, 8)))}.get(module, ()))
            if module == reject:
                break
            completed.append(module)
        if entry.get("compiled_modules") != completed:
            raise ValueError("Fr compiled module closure is incomplete")
        if reject:
            stage = ("discarded-carry-propagation-guard" if case == "wrong-discarded-carry" else
                     "source-decomposition" if case == "wrong-suffix-connection" else "arithmetic-proof")
            if entry.get("rejected_at") != reject or entry.get("rejection_stage") != stage:
                raise ValueError("Fr negative-control stage is missing or incorrect")
        else:
            audit = support / "FrAudit.v"
            expected_audit = ("From Stdlib Require Import ZArith.\nRequire Import " + " ".join(fr_native.MODULE_ROOTS) + ".\n"
                              + f'Example fr_identity : FrFirstReduction.fr_modulus = ({int(config["fields"]["fr"])})%Z := eq_refl.\n'
                              + "\n".join("Print Assumptions " + root + "." for root in fr_native.ROOTS) + "\n")
            if audit.read_text() != expected_audit:
                raise ValueError("Fr assumption or modulus audit changed")
            files.append(audit)
            required_artifacts.add(str((support / "FrAudit.vo").resolve(strict=True)))
        required_sources.update(str(path.resolve(strict=True)) for path in files)
        required_artifacts.add(str(extracted.with_suffix(".vo").resolve(strict=True)))
        required_artifacts.update(str((support / (name + ".vo")).resolve(strict=True)) for name in completed[1:])
    if set(report.get("sources", {})) != required_sources or set(report.get("compiled_artifacts", {})) != required_artifacts:
        raise ValueError("Fr source or compiled-artifact inventory is incomplete")
    for category in ("sources", "compiled_artifacts", "execution_artifacts"):
        native.validate_artifact_hashes(report[category])


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
        work = formal.WORK / "decaf-fr-fiat-bridge"
        work.mkdir(parents=True, exist_ok=True)
        report_path = work / "report.json"
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "scope": "exact canonical Rust32 Fr multiplication output equality with the exact-options Fiat pipeline in the supplied Core semantics",
                  "kernel_reduction": "recursive Rocq kernel checking with bytecode reduction enabled; Fiat proof terms retain explicit Rocq VM/compiler trust",
                  "open_obligations": ["native execution and extraction semantics", "native overflow/panic safety and termination",
                                       "Go arithmetic correspondence and remaining field operations", "group, encoding, compiled traces and consumer closure"],
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
            native_dir = formal.WORK / "decaf-fr-field-proof"
            native_path = native_dir / "report.json"
            native_report = json.loads(native_path.read_text())
            validate_native_receipt(native_report, native_dir)
            config_path = formal.ROOT / "decaf/proofs/toolchain.json"
            config = json.loads(config_path.read_text())
            generation_path = formal.WORK / "decaf-fields/report.json"
            generation = json.loads(generation_path.read_text())
            fiat.validate_generation(config, generation, generation_path.parent)
            if formal.file_digest(native_dir / "original/fiat.rs") != formal.file_digest(
                    generation_path.parent / "rust/fr.rs"):
                raise ValueError("native multiplication source differs from the exact Fiat recipe output")
            build_path = formal.WORK / "decaf-fiat-build/report.json"
            build = json.loads(build_path.read_text())
            patch = formal.ROOT / "decaf/proofs/fiat-array-index.patch"
            fiat_source = fiat.validate_proof_build(config_path, build, patch)
            if (native_report["input_hashes"][str(generation_path.resolve())] != formal.file_digest(generation_path) or
                    native_report["input_hashes"][str(build_path.resolve())] != formal.file_digest(build_path)):
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
            fq_original = formal.WORK / "decaf-field-proof-replay/original"
            flags = ["-Q", fiat_source / "src", "Crypto", "-Q", fiat_source / "coqprime/src/Coqprime", "Coqprime",
                     "-Q", fiat_source / "rupicola/bedrock2/deps/coqutil/src/coqutil", "coqutil",
                     "-Q", fiat_source / "rewriter/src/Rewriter", "Rewriter",
                     "-Q", formal.CACHE / "record-update/src", "RecordUpdate",
                     "-Q", fq_original / "support", "Core", "-Q", fq_original / "proofs/coq/extraction", "Slice",
                     "-Q", original / "support", "", "-Q", original / "proofs/coq/extraction", "FrSlice",
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
