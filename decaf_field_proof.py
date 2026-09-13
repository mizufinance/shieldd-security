#!/usr/bin/env python3
"""Replay native Rust Fq addition, helper arithmetic, and array-access proofs."""
import json
import os
from pathlib import Path
import re
import shutil

import formal
from decaf_toolchain import hax_tool_paths, native_artifact
from decaf_fiat_proof import validate_generation, validate_proof_build
from decaf_inventory import atomic_json, CACHES, MATRIX, validate
from decaf_native_prefix import multiplication_prefix, multiplication_rounds
from security import bounded_run

ROOT = formal.ROOT
PROOFS = ROOT / "decaf/proofs"
MODULES = ("Core", "Carry", "RustBorrow", "RustMultiplyZero", "RustMultiply", "RustSelect", "RustFiatPrimitives",
           "RustArray", "RustMultiplyWords", "RustFieldAdd", "RustMultiplyRow", "RustFirstReduction", "RustMultiplyRound")
ROOTS = tuple("Core." + name for name in (
    "Carry.addcarry_exact", "Carry.addcarry_safety", "Carry.addcarry_reconstruction",
    "RustBorrow.borrow_exact", "RustBorrow.borrow_safety", "RustBorrow.borrow_reconstruction",
    "RustMultiply.multiply_exact", "RustMultiply.multiply_safety", "RustMultiply.multiply_reconstruction",
    "RustMultiplyZero.multiply_zero_witness",
    "RustSelect.select_exact", "RustSelect.select_safety", "RustArray.update_length",
    "RustFieldAdd.add_correct", "RustFieldAdd.add_accesses")) + tuple(
        "Core.RustFiatPrimitives." + name for name in (
            "fiat_cast32", "fiat_cast_bit", "multiply_fiat", "addcarry_fiat", "select_fiat", "borrow_fiat",
            "multiply_high_room", "carry_high_add", "carry_carry_add")) + tuple(
        "Core.RustMultiplyWords." + name for name in ("mul_output_words", "mul_output_length", "mul_accesses")) + tuple(
        "Core.RustMultiplyRow." + name for name in ("first_row_correct", "first_row_decomposition", "first_row_length", "first_row_words")) + tuple(
        "Core.RustFirstReduction." + name for name in (
            "first_redc_decomposition", "first_redc_correct", "first_redc_length", "first_redc_words",
            "first_redc_bound", "nine_words_top_zero", "first_redc_top_zero", "redc_state_length", "redc_state_carry")) + tuple(
        "Core.RustMultiplyRound." + name for name in (
            "add9_correct", "round_product_decomposition", "round_sum_decomposition", "round_redc_decomposition",
            "finish_value", "round_correct", "round_shape", "round_bound", "round_top_zero"))


def definition(text, name):
    match = re.search(r"^Definition " + re.escape(name) + r"\b.*?(?=^Definition |\Z)", text, re.M | re.S)
    if not match:
        raise ValueError("missing extracted definition: " + name)
    return match[0]


def validate_accesses(text):
    if re.search(r"\b(failure|Admitted|Axiom)\b|NotImplementedYet|TODO", text):
        raise ValueError("unsupported extraction")
    body = definition(text, "fq_add")
    if body.count("t_Array (t_u32) ((8 : t_usize))") != 4:
        raise ValueError("unexpected array representation")
    reads = re.findall(r"f_index \((arg[12])\) \(\((\d+) : t_usize\)\)", body)
    if reads != [(name, str(i)) for i in range(8) for name in ("arg1", "arg2")]:
        raise ValueError("reads do not match the proved access schedule")
    writes = re.findall(r"update_at_usize \(out1\) \(\((\d+) : t_usize\)\)", body)
    if writes != list(map(str, range(8))):
        raise ValueError("writes do not match the proved access schedule")
    expected = {"fq_addcarryx_u32": 8, "fq_subborrowx_u32": 9, "fq_cmovznz_u32": 8,
                "f_index": 16, "update_at_usize": 8, "cast": 1}
    calls = re.findall(r"\b(?:fq_(?!add\b)\w+|f_\w+|update_at_usize|cast)\b", body)
    if {name: calls.count(name) for name in set(calls)} != expected:
        raise ValueError("body no longer matches the reviewed safety composition")


def modulus_mutation(source):
    start = source.index("pub const fn fq_add(")
    end = source.index("\n}", start) + 2
    body = source[start:end]
    old = "fq_subborrowx_u32(&mut x17, &mut x18, 0x0, x1, (0x1 as u32));"
    if body.count(old) != 1:
        raise ValueError("modulus mutation no longer matches the source")
    return source[:start] + body.replace(old, old.replace("0x1 as", "0x2 as")) + source[end:]


def multiplication_mutation(source):
    start = source.index("pub const fn fq_mulx_u32(")
    end = source.index("\n}", start) + 2
    body = source[start:end]
    old = "let x1: u64 = ((arg1 as u64) * (arg2 as u64));"
    if body.count(old) != 1:
        raise ValueError("multiplication mutation no longer matches the source")
    new = "let x1: u64 = (((arg1 as u64) * (arg2 as u64)) + 1);"
    return source[:start] + body.replace(old, new) + source[end:]


def row_carry_mutation(source):
    start = source.index("pub const fn fq_mul(")
    end = source.index("\n}", start) + 2
    body = source[start:end]
    old = "fq_addcarryx_u32(&mut x25, &mut x26, 0x0, x24, x21);"
    if body.count(old) != 1:
        raise ValueError("row-carry mutation no longer matches the source")
    return source[:start] + body.replace(old, old.replace("x24, x21", "x24, x22")) + source[end:]


def validate_mul_accesses(text):
    body = definition(text, "fq_mul")
    if body.count("t_Array (t_u32) ((8 : t_usize))") != 4:
        raise ValueError("unexpected multiplication array representation")
    reads = re.findall(r"f_index \((arg[12])\) \(\((\d+) : t_usize\)\)", body)
    expected_reads = [("arg1", str(i)) for i in (*range(1, 8), 0)]
    expected_reads += [("arg2", str(i)) for _ in range(8) for i in range(7, -1, -1)]
    if reads != expected_reads:
        raise ValueError("multiplication reads differ from the proved bounded schedule")
    writes = re.findall(r"update_at_usize \(out1\) \(\((\d+) : t_usize\)\)", body)
    if writes != list(map(str, range(8))):
        raise ValueError("multiplication writes differ from the proved bounded schedule")
    calls = re.findall(r"\b(?:fq_(?!mul\b)\w+|f_\w+|update_at_usize|cast)\b", body)
    expected = {"fq_mulx_u32": 128, "fq_addcarryx_u32": 239, "fq_subborrowx_u32": 9,
                "fq_cmovznz_u32": 8, "f_add": 23, "cast": 31, "f_index": 72, "update_at_usize": 8}
    if {name: calls.count(name) for name in set(calls)} != expected:
        raise ValueError("multiplication operation inventory changed")


def validate_assumptions(text):
    if [s.strip() for s in text.splitlines() if s.strip()] != [
            "Closed under the global context"] * len(ROOTS):
        raise ValueError("native field theorem assumptions are not closed")


def validate_rejection(text, expected_path="RustFieldAdd.v"):
    failures = re.findall(r'^File "([^"\n]+)", line \d+, characters \d+-\d+:\n'
                          r'Error: Tactic failure:[ \t]+Cannot find witness\.(?:\n|$)', text, re.M)
    if failures != [str(expected_path)] or len(re.findall(r'^Error:', text, re.M)) != 1:
        raise ValueError("mutation failed outside field arithmetic checking")


def expected_failure(error, code):
    return code in (1, 101) and str(error).startswith(f"verification process failed ({code}); see ")


def validate_case_files(work, cases, proof_hashes):
    for case_name, case_report in cases.items():
        case = work / case_name
        if case_report["input_hashes"] != {
                name: formal.file_digest(case / name) for name in case_report["input_hashes"]}:
            raise ValueError("native case inputs changed during replay")
        if case_report["extraction_sha256"] != formal.file_digest(
                case / "proofs/coq/extraction/Decaf_proof_slice_Fiat.v"):
            raise ValueError("native extraction changed during replay")
        if set(case_report["derived_sources"]) != {"NativeMultiplyPrefix.v"} or case_report["derived_sources"] != {
                name: formal.file_digest(case / "proofs/coq/extraction" / name)
                for name in case_report["derived_sources"]}:
            raise ValueError("derived native checkpoint sources changed during replay")
        if proof_hashes != {
                name: formal.file_digest(case / "support" / (name + ".v")) for name in proof_hashes}:
            raise ValueError("compiled proof copies differ from the reviewed sources")


def validate_artifact_hashes(hashes):
    if not hashes:
        raise ValueError("empty execution/import artifact inventory")
    for name, digest in hashes.items():
        path = Path(name)
        if path.resolve(strict=True) != path or formal.file_digest(path) != digest:
            raise ValueError("execution/import artifact changed: " + name)


def rust_toolchain(command, name, host):
    executables = {tool: Path(command(["rustup", "which", "--toolchain", name, tool]).strip()).resolve(strict=True)
                   for tool in ("rustc", "cargo", "rustdoc")}
    sysroot = Path(command([executables["rustc"], "--print", "sysroot"]).strip()).resolve(strict=True)
    suffix = {"x86_64-unknown-linux-gnu": "so", "aarch64-apple-darwin": "dylib"}.get(host)
    if suffix is None:
        raise ValueError("unsupported Rust proof host: " + host)
    drivers = sorted((sysroot / "lib").glob("librustc_driver*." + suffix))
    if not drivers:
        raise ValueError("missing Rust compiler driver artifacts")
    artifacts = {str(path.resolve(strict=True)): formal.file_digest(path)
                 for path in [*executables.values(), *drivers]}
    return executables, artifacts, sysroot / "lib"


def main():
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-field-proof-replay"
        work.mkdir(parents=True, exist_ok=True)
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "scope": "Rust32 Fq addition, native helpers, Fiat primitive correspondence and the first native multiplication/reduction prefixes on 64-bit targets; full multiplication remains open",
                  "theorem_roots": ROOTS, "commands": [], "cases": {}}
        report_path = work / "report.json"
        atomic_json(report_path, report)
        env = dict(os.environ, CARGO_BUILD_JOBS="1", RAYON_NUM_THREADS="1",
                   GIT_NO_REPLACE_OBJECTS="1", COQPATH="", OCAMLPATH="",
                   CARGO_CACHE_RUSTC_INFO="0",
                   CARGO_TARGET_DIR=str(formal.CACHE / "decaf-proof-target"))
        for name in ("RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"):
            env.pop(name, None)

        def command(args, cwd=work, expect_failure=False, failure_code=1):
            index = len(report["commands"])
            report["commands"].append(list(map(str, args)))
            atomic_json(report_path, report)
            log = work / f"{index:02}.log"
            failed = False
            try:
                bounded_run(list(map(str, args)), cwd, env, log, work / "unused", work, 300)
            except RuntimeError as error:
                if not expect_failure or not expected_failure(error, failure_code):
                    raise
                failed = True
            if failed != expect_failure:
                raise RuntimeError(f"unexpected command status; see {log.name}")
            return log.read_text()

        try:
            for child in work.iterdir():
                if child == report_path:
                    continue
                if child.is_dir() and not child.is_symlink():
                    shutil.rmtree(child)
                else:
                    child.unlink()
            config = json.loads((PROOFS / "toolchain.json").read_text())
            report["toolchain"] = config
            report["runner_sha256"] = formal.file_digest(Path(__file__))
            report["toolchain_selector_sha256"] = formal.file_digest(ROOT / "decaf_toolchain.py")
            helpers = ("decaf_fiat_proof.py", "decaf_fiat_build.py", "decaf_go_proof.py",
                       "formal.py", "security.py", "decaf_inventory.py", "decaf_toolchain.py", "decaf_native_prefix.py")
            report["helper_hashes"] = {name: formal.file_digest(ROOT / name) for name in helpers}
            generated = formal.WORK / "decaf-fields"
            receipt_path = generated / "report.json"
            receipt = json.loads(receipt_path.read_text())
            validate_generation(config, receipt, generated)
            fiat_build_path = formal.WORK / "decaf-fiat-build/report.json"
            fiat_build = json.loads(fiat_build_path.read_text())
            fiat_source = validate_proof_build(PROOFS / "toolchain.json", fiat_build,
                                               PROOFS / "fiat-array-index.patch")
            report["fiat_proof_build_receipt_sha256"] = formal.file_digest(fiat_build_path)
            report["fiat_proof_build"] = fiat_build
            if receipt.get("status") != "generated" or receipt.get("completed") is not True:
                raise ValueError("native generation is incomplete")
            generator = native_artifact(config, "fiat")
            if receipt.get("native_host", "aarch64-apple-darwin") != generator["host"]:
                raise ValueError("native generation host does not match the selected artifact")
            if receipt["fiat_revision"] != config["fiat"]["revision"] or receipt["generator_sha256"] != generator["binary_sha256"]:
                raise ValueError("native generation uses an unrecognized toolchain")
            entry, = [e for e in receipt["outputs"] if e["path"] == "rust/fq.rs"]
            source_path = generated / "rust/fq.rs"
            if formal.file_digest(source_path) != entry["sha256"] or entry["command"][-3:] != ["fq", "32", config["fields"]["fq"]]:
                raise ValueError("native source does not match the shared field parameters")
            report["generation_receipt_sha256"] = formal.file_digest(receipt_path)
            source = source_path.read_text()
            matrix = json.loads(MATRIX.read_text())
            validate(matrix)
            rust_source = matrix["sources"]["rust"]
            cache, bare = CACHES["rust"]
            if not bare or rust_source["role"] != "candidate":
                raise ValueError("expected an immutable Rust candidate in the bare source cache")
            source_log = work / f"{len(report['commands']):02}.log"
            command(["git", "--git-dir", cache, "show",
                     rust_source["revision"] + ":src/fields/fq/u32/generated.rs"])
            if formal.file_digest(source_log) != entry["sha256"]:
                raise ValueError("adopted Rust Fq bytes differ from the generated proof source")
            report["adopted_rust_source"] = rust_source
            report["matrix_sha256"] = formal.file_digest(MATRIX)
            hax = ["opam", "exec", "--switch=hax-0.3.7", "--"]
            build = native_artifact(config, "hax")
            report["native_host"] = build["host"]
            paths = hax_tool_paths(command, hax)
            for tool, digest in build["binary_sha256"].items():
                if formal.file_digest(paths[tool]) != digest:
                    raise ValueError("unrecognized hax artifact: " + tool)
            env["HAX_ENGINE_BINARY"] = str(paths["hax-engine"])
            report["hax_tool_paths"] = {tool: str(path) for tool, path in paths.items()}
            report["execution_artifacts"] = {str(paths[tool]): digest for tool, digest in build["binary_sha256"].items()}
            extraction_tools, extraction_artifacts, extraction_lib = rust_toolchain(command, config["hax"]["rust"], build["host"])
            test_tools, test_artifacts, test_lib = rust_toolchain(command, config["rust_test"], build["host"])
            report["rust_tool_paths"] = {role: {name: str(path) for name, path in selected.items()}
                                        for role, selected in (("extraction", extraction_tools), ("tests", test_tools))}
            report["execution_artifacts"].update(extraction_artifacts)
            report["execution_artifacts"].update(test_artifacts)
            env["PATH"] = str(extraction_tools["cargo"].parent) + os.pathsep + env["PATH"]
            env["RUSTUP_TOOLCHAIN"] = config["hax"]["rust"]
            loader_variable = "LD_LIBRARY_PATH" if build["host"].endswith("linux-gnu") else "DYLD_LIBRARY_PATH"
            report["rust_driver_search"] = {"variable": loader_variable,
                                             "extraction": str(extraction_lib), "tests": str(test_lib)}
            if Path(command([*hax, "which", "cargo"]).strip()).resolve(strict=True) != extraction_tools["cargo"]:
                raise ValueError("hax dispatch does not select the bound Cargo executable")
            hax_cli = [*hax, str(paths["cargo-hax"]), "hax"]
            version = command([extraction_tools["rustc"], "-Vv"])
            report["rust_extraction_version"] = version
            if config["hax"]["rust_commit"] not in version or build["host"] not in version:
                raise ValueError("unexpected extraction compiler")
            env["CARGO_BUILD_TARGET"] = build["host"]
            report["rust_test_version"] = command([test_tools["rustc"], "-Vv"])
            rocq = ["opam", "exec", "--switch=decaf-fv", "--", "rocq"]
            rocq_driver = Path(command(["opam", "exec", "--switch=decaf-fv", "--", "which", "rocq"]).strip()).resolve(strict=True)
            if (str(rocq_driver) != fiat_build["compiler"]["path"] or
                    formal.file_digest(rocq_driver) != fiat_build["compiler"]["sha256"] or
                    command([*rocq, "-v"]) != fiat_build["rocq_version"]):
                raise ValueError("Rocq differs from the source-bound Fiat proof build")
            rocq[-1] = str(rocq_driver)
            report["execution_artifacts"][str(rocq_driver)] = formal.file_digest(rocq_driver)
            rocq_lib = Path(command(["opam", "var", "lib", "--switch=decaf-fv"]).strip()).resolve(strict=True)
            rocq_worker = (rocq_lib / "rocq-runtime/rocqworker").resolve(strict=True)
            rocq_checker = Path(command([*rocq[:-1], "which", "rocqchk"]).strip()).resolve(strict=True)
            for artifact in (rocq_worker, rocq_checker):
                report["execution_artifacts"][str(artifact)] = formal.file_digest(artifact)
            compile_rocq = [*rocq[:-1], rocq_worker, "--kind=compile"]
            check_rocq = [*rocq[:-1], rocq_checker]
            installed = command(["opam", "list", "--switch=decaf-fv", "--installed", "--columns=version", "--short", "rocq-runtime"]).strip()
            if installed != config["rocq-runtime"]:
                raise ValueError("unexpected Rocq version")
            records = formal.CACHE / "record-update/src"
            if command(["git", "rev-parse", "HEAD"], records.parent).strip() != config["record_update"]["revision"]:
                raise ValueError("unexpected record-update revision")
            command(["git", "diff", "--exit-code", "HEAD", "--", "src"], records.parent)
            report["record_update_sources"] = {name: formal.file_digest(records / (name + ".v"))
                                                for name in ("RecordEta", "RecordSet")}
            for name in ("RecordEta", "RecordSet"):
                command([*compile_rocq, "-Q", records, "RecordUpdate", records / (name + ".v")])
            report["compiled_artifacts"] = {str((records / (name + ".vo")).resolve(strict=True)):
                                             formal.file_digest(records / (name + ".vo"))
                                             for name in ("RecordEta", "RecordSet")}
            report["proof_hashes"] = {name: formal.file_digest(PROOFS / "rocq" / (name + ".v")) for name in MODULES}
            modulus = int(config["fields"]["fq"])
            limbs = [(modulus - 1 >> (32*i)) & ((1 << 32)-1) for i in range(8)]
            product_witness = ((1 + (1 << 32)) * pow(1 << 256, -1, modulus)) % modulus
            product_limbs = [(product_witness >> (32*i)) & ((1 << 32)-1) for i in range(8)]
            for case_name in ("original", "wrong-modulus", "wrong-multiplication", "wrong-row-carry"):
                mutation = case_name != "original"
                case = work / case_name
                case.mkdir()
                (case / "Cargo.toml").write_text('[package]\nname="decaf_proof_slice"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
                changed = (modulus_mutation(source) if case_name == "wrong-modulus" else
                           multiplication_mutation(source) if case_name == "wrong-multiplication" else
                           row_carry_mutation(source) if case_name == "wrong-row-carry" else source)
                (case / "fiat.rs").write_text(changed)
                (case / "lib.rs").write_text('#![no_std]\npub mod fiat;\n#[test] fn modulus_witness() { let mut z=[0u32;8]; fiat::fq_add(&mut z,&' + str(limbs) + ',&[1,0,0,0,0,0,0,0]); assert_eq!(z,[0u32;8]); }\n'
                    '#[test] fn multiplication_witness() { let (mut lo,mut hi)=(0u32,0u32); fiat::fq_mulx_u32(&mut lo,&mut hi,0,0); assert_eq!((lo,hi),(0,0)); }\n'
                    '#[test] fn row_carry_witness() { let mut z=[0u32;8]; fiat::fq_mul(&mut z,&[1,0,0,0,0,0,0,0],&[1,1,0,0,0,0,0,0]); assert_eq!(z,' + str(product_limbs) + '); }\n')
                report["cases"][case.name] = {"source_sha256": formal.file_digest(case / "fiat.rs")}
                report["cases"][case.name]["input_hashes"] = {
                    name: formal.file_digest(case / name) for name in ("Cargo.toml", "lib.rs", "fiat.rs")}
                env["RUSTC"] = str(test_tools["rustc"])
                env["RUSTDOC"] = str(test_tools["rustdoc"])
                env[loader_variable] = str(test_lib)
                witness = command([test_tools["cargo"], "test", "--release", "--", "--test-threads=1"],
                                  case, mutation, failure_code=101)
                witness_name = ("multiplication_witness" if case_name == "wrong-multiplication" else
                                "row_carry_witness" if case_name == "wrong-row-carry" else "modulus_witness")
                if mutation and witness_name + " ... FAILED" not in witness:
                    raise ValueError("mutant did not fail its native arithmetic witness")
                env["RUSTC"] = str(extraction_tools["rustc"])
                env[loader_variable] = str(extraction_lib)
                command([*hax_cli, "into", "-i", "-** +decaf_proof_slice::fiat::fq_mul +decaf_proof_slice::fiat::fq_add", "coq"], case)
                extraction = case / "proofs/coq/extraction"
                extracted = extraction / "Decaf_proof_slice_Fiat.v"
                validate_accesses(extracted.read_text())
                validate_mul_accesses(extracted.read_text())
                report["cases"][case.name]["extraction_sha256"] = formal.file_digest(extracted)
                derived = extraction / "NativeMultiplyPrefix.v"
                derived.write_text(multiplication_prefix(extracted.read_text()) + multiplication_rounds(extracted.read_text()))
                report["cases"][case.name]["derived_sources"] = {derived.name: formal.file_digest(derived)}
                support = case / "support"
                support.mkdir()
                flags = ["-Q", fiat_source / "src", "Crypto",
                         "-Q", fiat_source / "rewriter/src/Rewriter", "Rewriter",
                         "-Q", fiat_source / "coqprime/src/Coqprime", "Coqprime",
                         "-Q", fiat_source / "rupicola/bedrock2/deps/coqutil/src/coqutil", "coqutil",
                         "-Q", support, "Core", "-Q", records, "RecordUpdate", "-Q", extraction, "Slice"]
                for name in MODULES:
                    shutil.copyfile(PROOFS / "rocq" / (name + ".v"), support / (name + ".v"))
                command([*compile_rocq, *flags, support / "Core.v"])
                command([*compile_rocq, *flags, extracted])
                command([*compile_rocq, *flags, derived])
                for artifact in (support / "Core.vo", extracted.with_suffix(".vo"), derived.with_suffix(".vo")):
                    report["compiled_artifacts"][str(artifact.resolve(strict=True))] = formal.file_digest(artifact)
                for name in MODULES[1:]:
                    rejected = ((case_name == "wrong-modulus" and name == "RustFieldAdd") or
                                (case_name == "wrong-multiplication" and name == "RustMultiplyZero") or
                                (case_name == "wrong-row-carry" and name == "RustMultiplyRow"))
                    output = command([*compile_rocq, *flags, support / (name + ".v")], expect_failure=rejected)
                    if rejected:
                        validate_rejection(output, support / (name + ".v"))
                        break
                    artifact = support / (name + ".vo")
                    report["compiled_artifacts"][str(artifact.resolve(strict=True))] = formal.file_digest(artifact)
                if not mutation:
                    audit = support / "Audit.v"
                    audit.write_text("From Core Require Import " + " ".join(MODULES) + ".\n" + "\n".join(
                        "Print Assumptions " + root + "." for root in ROOTS) + "\n")
                    validate_assumptions(command([*compile_rocq, *flags, audit]))
                    report["compiled_artifacts"][str(audit.with_suffix(".vo").resolve(strict=True))] = formal.file_digest(audit.with_suffix(".vo"))
                    original_flags = flags
            validate_artifact_hashes(report["compiled_artifacts"])
            validate_artifact_hashes(report["execution_artifacts"])
            command([*check_rocq, "-bytecode-compiler", "no", "-silent", *original_flags,
                     *("Core." + name for name in MODULES), "Core.Audit"])
            validate_proof_build(PROOFS / "toolchain.json", fiat_build, PROOFS / "fiat-array-index.patch")
            if formal.file_digest(fiat_build_path) != report["fiat_proof_build_receipt_sha256"]:
                raise ValueError("Fiat build receipt changed during replay")
            validate_artifact_hashes(report["compiled_artifacts"])
            validate_artifact_hashes(report["execution_artifacts"])
            if hax_tool_paths(command, hax) != paths:
                raise ValueError("hax dispatch paths changed during replay")
            if Path(command([*hax, "which", "cargo"]).strip()).resolve(strict=True) != extraction_tools["cargo"]:
                raise ValueError("hax Cargo dispatch changed during replay")
            if report["runner_sha256"] != formal.file_digest(Path(__file__)):
                raise ValueError("replay runner changed during execution")
            validate_case_files(work, report["cases"], report["proof_hashes"])
            if formal.file_digest(rocq_driver) != fiat_build["compiler"]["sha256"]:
                raise ValueError("Rocq driver changed during replay")
            if report["proof_hashes"] != {name: formal.file_digest(PROOFS / "rocq" / (name + ".v")) for name in MODULES}:
                raise ValueError("handwritten proofs changed during replay")
            if report["record_update_sources"] != {name: formal.file_digest(records / (name + ".v")) for name in ("RecordEta", "RecordSet")}:
                raise ValueError("record-update source changed during replay")
            if report["generation_receipt_sha256"] != formal.file_digest(receipt_path):
                raise ValueError("generation receipt changed during replay")
            if report["matrix_sha256"] != formal.file_digest(MATRIX):
                raise ValueError("adopted source inventory changed during replay")
            validate_generation(config, receipt, generated)
            if report["helper_hashes"] != {name: formal.file_digest(ROOT / name) for name in helpers}:
                raise ValueError("replay helper changed during execution")
            report.update(status="passed", completed=True)
        except Exception as error:
            report["detail"] = str(error)
        finally:
            atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
