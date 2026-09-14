#!/usr/bin/env python3
"""Source-bound Rust Fr multiplication replay in the supplied Core semantics."""
import json
import os
from pathlib import Path
import re
import shutil

import formal
import decaf_field_proof as native
import decaf_fiat_proof as fiat
import decaf_native_fiat_bridge as parent
from decaf_fr_native_prefix import multiplication_checkpoints, DERIVED_MODULES
from decaf_inventory import atomic_json, MATRIX, CACHES
from security import bounded_run

MODULE_ROOTS = {
    "FrHelpers": ("fr_multiply_same", "fr_carry_same", "fr_borrow_same", "fr_select_same",
                  "fr_first_row_same", "fr_first_row_decomposition"),
    "FrFirstReduction": ("fr_first_redc_correct",),
    "FrReductionBounds": ("fr_first_redc_length", "fr_first_redc_words", "fr_first_redc_bound",
                          "fr_nine_words_top_zero", "fr_first_redc_top_zero", "fr_redc_state_length", "fr_redc_state_carry"),
    "FrRound": ("fr_add9_same", "fr_add9_correct", "fr_round_product_decomposition",
                "fr_round_sum_decomposition", "fr_round_redc_decomposition", "fr_round_correct",
                "fr_round_shape", "fr_round_bound", "fr_round_top_zero"),
    "FrFinal": ("fr_final_correct", "fr_final_state_independent"),
    "FrChain": ("fr_rounds_correct", "fr_accumulator_correct"),
    "FrTail": ("fr_first_redc_decomposition", *(f"fr_round{i}_decomposition" for i in range(1, 8)),
               "fr_initial_tail_decomposition"),
    "FrComplete": ("fr_body_decomposition", "fr_multiplication_correct", "fr_output_state_independent"),
}
ROOTS = tuple(module + "." + name for module, names in MODULE_ROOTS.items() for name in names)
MUTATIONS = {
    "wrong-coefficient": ("fr_mulx_u32(&mut x40, &mut x41, x23, 0x70e3da01);",
                          "fr_mulx_u32(&mut x40, &mut x41, x23, 0x70e3da02);"),
    "wrong-discarded-carry": ("fr_addcarryx_u32(&mut x75, &mut x76, x74, x25, x58);",
                              "fr_addcarryx_u32(&mut x75, &mut x76, 0x0, x25, x58);"),
    "wrong-final-selection": ("fr_cmovznz_u32(&mut x816, x815, x798, x781);",
                              "fr_cmovznz_u32(&mut x816, x815, x781, x798);"),
}
CASES = ("original", *MUTATIONS, "wrong-suffix-connection")


def mutate_source(source, case):
    if case not in MUTATIONS:
        if case not in CASES:
            raise ValueError("unknown Fr case")
        return source
    start = source.index("pub const fn fr_mul(")
    end = source.index("\n}", start) + 2
    body = source[start:end]
    old, new = MUTATIONS[case]
    if body.count(old) != 1:
        raise ValueError("Fr source control no longer matches")
    return source[:start] + body.replace(old, new) + source[end:]


def suffix_mutation(derived):
    result = dict(derived)
    name = "FrSuffixDefinition7.v"
    old = "let x7 := f_index arg1 ((7 : t_usize)) in"
    if result[name].count(old) != 1:
        raise ValueError("Fr suffix control no longer matches")
    result[name] = result[name].replace(old, old.replace("((7 :", "((6 :"))
    return result


def witness_source(modulus):
    def words(value):
        return "[" + ",".join(str((value >> (32*i)) % (2**32)) for i in range(8)) + "]"
    values = sorted({0, 1, modulus-1, modulus-2, modulus//2,
                     *((2**i+d) % modulus for i in range(0, 256, 32) for d in (-1, 0, 1))})
    inverse = pow(2**256, -1, modulus)
    vectors = ",\n".join(f"({words(a)},{words(b)},{words(a*b*inverse % modulus)})"
                          for a in values for b in values)
    return ('#![no_std]\npub mod fiat;\n#[test] fn multiplication_witnesses(){\n'
            'let vectors: &[([u32;8],[u32;8],[u32;8])]= &[\n' + vectors + '];\n'
            'for (i,(a,b,expected)) in vectors.iter().enumerate(){let mut out=[0u32;8];'
            'fiat::fr_mul(&mut out,a,b);assert_eq!(&out,expected,"vector {}",i);}\n}\n')


def validate_extraction(text):
    if re.search(r"\b(failure|Admitted|Axiom)\b|NotImplementedYet|TODO", text):
        raise ValueError("unsupported Fr extraction")
    body = native.definition(text, "fr_mul")
    operations = {"fr_mulx_u32": 136, "fr_addcarryx_u32": 247, "fr_subborrowx_u32": 9,
                  "fr_cmovznz_u32": 8, "f_add": 23, "cast": 31, "f_index": 72, "update_at_usize": 8}
    if any(len(re.findall(r"\b" + name + r"\b", body)) != count for name, count in operations.items()):
        raise ValueError("Fr multiplication operation inventory changed")
    reads = re.findall(r"f_index \((arg[12])\) \(\((\d+) : t_usize\)\)", body)
    expected = [("arg1", str(i)) for i in (*range(1, 8), 0)]
    expected += [("arg2", str(i)) for _ in range(8) for i in range(7, -1, -1)]
    writes = re.findall(r"update_at_usize \(out1\) \(\((\d+) : t_usize\)\)", body)
    if reads != expected or writes != list(map(str, range(8))):
        raise ValueError("Fr array access inventory changed")


def validate_closed(text):
    if [line.strip() for line in text.splitlines() if line.strip()] != ["Closed under the global context"] * len(ROOTS):
        raise ValueError("Fr transitive assumptions are not closed")


def validate_rejection(text, path, case):
    if case not in CASES[1:]:
        raise ValueError("unknown Fr rejection case")
    if case == "wrong-suffix-connection":
        native.validate_connection_rejection(text, str(path))
        return
    if case == "wrong-final-selection":
        native.validate_rejection(text, str(path))
        return
    reason = (r"Tactic failure: Fr discarded carry is not propagated\." if case == "wrong-discarded-carry"
              else r"No matching clauses for match\.")
    failures = re.findall(r'^File "([^"\n]+)", line \d+, characters \d+-\d+:\n'
                          + r'Error: ' + reason + r'(?:\n|$)', text, re.M)
    if failures != [str(path)] or text.count("Error:") != 1:
        raise ValueError("Fr control did not fail the expected reduction proof")


def validate_dispatch(command, base):
    hax = ["opam", "exec", "--switch=hax-0.3.7", "--"]
    selected = native.hax_tool_paths(command, hax)
    if {name: str(path) for name, path in selected.items()} != base["hax_tool_paths"]:
        raise ValueError("Fr hax dispatch changed")
    cargo = Path(command([*hax, "which", "cargo"]).strip()).resolve(strict=True)
    if str(cargo) != base["rust_tool_paths"]["extraction"]["cargo"]:
        raise ValueError("Fr extraction Cargo dispatch changed")


def main():
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-fr-field-proof"
        work.mkdir(parents=True, exist_ok=True)
        report_path = work / "report.json"
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "scope": "complete extracted Rust32 Fr multiplication in the supplied Core semantics",
                  "open_obligations": ["native execution/extraction semantics, safety and termination",
                                       "exact Fiat Fr endpoint, Go arithmetic and complete consumer closure"],
                  "theorem_roots": ROOTS, "commands": [], "cases": {}, "compiled_artifacts": {}, "sources": {}}
        atomic_json(report_path, report)
        env = dict(os.environ, OPAMROOTISOK="1", COQPATH="", OCAMLPATH="", OCAMLRUNPARAM="s=2M,o=20,O=50",
                   CARGO_BUILD_JOBS="1", RAYON_NUM_THREADS="1", CARGO_CACHE_RUSTC_INFO="0", GIT_NO_REPLACE_OBJECTS="1")
        for name in ("RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"):
            env.pop(name, None)

        def command(args, cwd=work, failure_code=None, timeout=600):
            index = len(report["commands"])
            report["commands"].append(list(map(str, args)))
            atomic_json(report_path, report)
            logs = work / "logs"
            logs.mkdir(exist_ok=True)
            log = logs / f"{index:03}.log"
            native.validate_evidence_size(work)
            failed = False
            try:
                bounded_run(list(map(str, args)), cwd, env, log, work / "unused", logs, timeout)
            except RuntimeError as error:
                if failure_code is None or not native.expected_failure(error, failure_code):
                    raise
                failed = True
            native.validate_evidence_size(work)
            if failed != (failure_code is not None):
                raise ValueError("unexpected Fr command status")
            return log.read_text()

        def bind(path, category="sources"):
            report[category][str(path.resolve(strict=True))] = formal.file_digest(path)

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
            base = json.loads(native_path.read_text())
            parent.validate_native_receipt(base, native_dir)
            config_path = formal.ROOT / "decaf/proofs/toolchain.json"
            config = json.loads(config_path.read_text())
            generated = formal.WORK / "decaf-fields"
            generation_path = generated / "report.json"
            generation = json.loads(generation_path.read_text())
            fiat.validate_generation(config, generation, generated)
            build_path = formal.WORK / "decaf-fiat-build/report.json"
            build = json.loads(build_path.read_text())
            fiat_source = fiat.validate_proof_build(config_path, build, native.PROOFS / "fiat-array-index.patch")
            if (base["generation_receipt_sha256"] != formal.file_digest(generation_path) or
                    base["fiat_proof_build_receipt_sha256"] != formal.file_digest(build_path)):
                raise ValueError("Fr replay and native parent dependencies differ")
            helpers = {"decaf_fr_native_prefix.py", "decaf_native_fiat_bridge.py", *parent.HELPERS}
            inputs = [Path(__file__), native_path, config_path, generation_path, build_path, MATRIX,
                      generated / "rust/fr.rs", *(formal.ROOT / name for name in sorted(helpers)),
                      *(native.PROOFS / "rocq" / (name + ".v") for name in MODULE_ROOTS)]
            report["input_hashes"] = {str(path.resolve(strict=True)): formal.file_digest(path) for path in inputs}
            report["native_parent_sha256"] = formal.file_digest(native_path)
            entry, = [item for item in generation["outputs"] if item["path"] == "rust/fr.rs"]
            if entry["command"][-3:] != ["fr", "32", config["fields"]["fr"]]:
                raise ValueError("Fr generation recipe changed")
            source = (generated / "rust/fr.rs").read_text()
            matrix = json.loads(MATRIX.read_text())
            cache, bare = CACHES["rust"]
            if not bare or matrix["sources"]["rust"] != base["adopted_rust_source"]:
                raise ValueError("Fr adopted candidate differs from native parent")
            log = work / "logs" / f'{len(report["commands"]):03}.log'
            command(["git", "--git-dir", cache, "show",
                     matrix["sources"]["rust"]["revision"] + ":src/fields/fr/u32/generated.rs"])
            if formal.file_digest(log) != entry["sha256"]:
                raise ValueError("adopted Fr source differs from generated source")
            report["adopted_rust_source"] = matrix["sources"]["rust"]
            report["execution_artifacts"] = base["execution_artifacts"]
            worker, = [Path(path) for path in base["execution_artifacts"] if Path(path).name == "rocqworker"]
            checker, = [Path(path) for path in base["execution_artifacts"] if Path(path).name == "rocqchk"]
            tool_paths = base["rust_tool_paths"]
            hax_paths = base["hax_tool_paths"]
            env["PATH"] = str(Path(tool_paths["extraction"]["cargo"]).parent) + os.pathsep + env["PATH"]
            env["RUSTUP_TOOLCHAIN"] = config["hax"]["rust"]
            env["CARGO_BUILD_TARGET"] = base["native_host"]
            env["HAX_ENGINE_BINARY"] = hax_paths["hax-engine"]
            validate_dispatch(command, base)
            flags = ["-Q", fiat_source / "src", "Crypto", "-Q", fiat_source / "rewriter/src/Rewriter", "Rewriter",
                     "-Q", fiat_source / "coqprime/src/Coqprime", "Coqprime",
                     "-Q", fiat_source / "rupicola/bedrock2/deps/coqutil/src/coqutil", "coqutil",
                     "-Q", formal.CACHE / "record-update/src", "RecordUpdate",
                     "-Q", native_dir / "original/support", "Core",
                     "-Q", native_dir / "original/proofs/coq/extraction", "Slice"]
            for case in CASES:
                directory = work / case
                directory.mkdir()
                (directory / "fiat.rs").write_text(mutate_source(source, case))
                (directory / "Cargo.toml").write_text('[package]\nname="decaf_fr_slice"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
                (directory / "lib.rs").write_text(witness_source(int(config["fields"]["fr"])))
                for name in ("fiat.rs", "Cargo.toml", "lib.rs"):
                    bind(directory / name)
                report["cases"][case] = {"source_sha256": formal.file_digest(directory / "fiat.rs"), "compiled_modules": []}
                env["CARGO_TARGET_DIR"] = str(formal.CACHE / "decaf-fr-proof-target")
                env["RUSTC"] = tool_paths["tests"]["rustc"]
                env["RUSTDOC"] = tool_paths["tests"]["rustdoc"]
                env[base["rust_driver_search"]["variable"]] = base["rust_driver_search"]["tests"]
                witness = command([tool_paths["tests"]["cargo"], "test", "--release", "--", "--test-threads=1"], directory,
                                  101 if case in MUTATIONS else None)
                if case in MUTATIONS and ("multiplication_witnesses ... FAILED" not in witness or
                                           "assertion `left == right` failed: vector" not in witness):
                    raise ValueError("Fr mutant did not fail its native arithmetic witness")
                env["RUSTC"] = tool_paths["extraction"]["rustc"]
                env["RUSTDOC"] = tool_paths["extraction"]["rustdoc"]
                env[base["rust_driver_search"]["variable"]] = base["rust_driver_search"]["extraction"]
                command(["opam", "exec", "--switch=hax-0.3.7", "--", hax_paths["cargo-hax"], "hax", "into", "-i",
                         "-** +decaf_fr_slice::fiat::fr_mul +decaf_fr_slice::fiat::fr_add", "coq"], directory)
                extraction = directory / "proofs/coq/extraction"
                support = directory / "support"
                support.mkdir()
                extracted = extraction / "Decaf_fr_slice_Fiat.v"
                validate_extraction(extracted.read_text())
                bind(extracted)
                derived = multiplication_checkpoints(extracted.read_text())
                if case == "wrong-suffix-connection":
                    derived = suffix_mutation(derived)
                for name, text in derived.items():
                    (support / name).write_text(text)
                    bind(support / name)
                for module in MODULE_ROOTS:
                    shutil.copyfile(native.PROOFS / "rocq" / (module + ".v"), support / (module + ".v"))
                    bind(support / (module + ".v"))
                case_flags = [*flags, "-Q", support, "", "-Q", extraction, "FrSlice"]
                compiler = ["opam", "exec", "--switch=decaf-fv", "--", worker, "--kind=compile", *case_flags]

                def compile_module(path):
                    command([*compiler, path])
                    bind(path.with_suffix(".vo"), "compiled_artifacts")
                    report["cases"][case]["compiled_modules"].append(path.stem)

                compile_module(extracted)
                compile_module(support / "FrPrefix.v")
                reject = ("FrFirstReduction" if case in ("wrong-coefficient", "wrong-discarded-carry") else
                          "FrFinal" if case == "wrong-final-selection" else
                          "FrTail" if case == "wrong-suffix-connection" else None)
                for module in MODULE_ROOTS:
                    dependencies = ({"FrRound": ("FrRoundDefinition",), "FrFinal": ("FrFinalDefinition",),
                                     "FrTail": ("FrAfterReductionDefinition", *(f"FrSuffixDefinition{i}" for i in range(1, 8)))}).get(module, ())
                    for dependency in dependencies:
                        compile_module(support / (dependency + ".v"))
                    if module == reject:
                        failure = command([*compiler, support / (module + ".v")], failure_code=1)
                        validate_rejection(failure, support / (module + ".v"), case)
                        report["cases"][case]["rejected_at"] = module
                        report["cases"][case]["rejection_stage"] = (
                            "discarded-carry-propagation-guard" if case == "wrong-discarded-carry" else
                            "source-decomposition" if case == "wrong-suffix-connection" else "arithmetic-proof")
                        break
                    compile_module(support / (module + ".v"))
                if case == "original":
                    audit = support / "FrAudit.v"
                    audit.write_text("From Stdlib Require Import ZArith.\nRequire Import " + " ".join(MODULE_ROOTS) + ".\n"
                                     + f'Example fr_identity : FrFirstReduction.fr_modulus = ({int(config["fields"]["fr"])})%Z := eq_refl.\n'
                                     + "\n".join("Print Assumptions " + root + "." for root in ROOTS) + "\n")
                    bind(audit)
                    validate_closed(command([*compiler, audit]))
                    bind(audit.with_suffix(".vo"), "compiled_artifacts")
                    command(["opam", "exec", "--switch=decaf-fv", "--", checker, "-silent", "-bytecode-compiler", "no",
                             *case_flags, *MODULE_ROOTS, "FrAudit"], timeout=1800)
            validate_dispatch(command, base)
            parent.validate_native_receipt(base, native_dir)
            fiat.validate_proof_build(config_path, build, native.PROOFS / "fiat-array-index.patch")
            fiat.validate_generation(config, generation, generated)
            for category in ("input_hashes", "execution_artifacts", "sources", "compiled_artifacts"):
                native.validate_artifact_hashes(report[category])
            if set(report["cases"]) != set(CASES):
                raise ValueError("incomplete Fr control inventory")
            report.update(status="passed", completed=True)
        except (Exception, KeyboardInterrupt) as error:
            report["detail"] = str(error) or "interrupted"
        finally:
            atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
