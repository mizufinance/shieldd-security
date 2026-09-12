#!/usr/bin/env python3
"""Replay the source-linked Rust carry proof and its incorrect-shift control."""
import json
import os
from pathlib import Path
import re
import shutil

import formal
from security import bounded_run

ROOT = formal.ROOT
CONFIG = ROOT / "decaf/proofs/toolchain.json"
SOURCE = "src/fields/fq/u32/fiat.rs"
ROOTS = ("addcarry_exact", "addcarry_safety", "addcarry_reconstruction")


def validate_extraction(text):
    if re.search(r"\b(failure|Admitted|Axiom)\b|NotImplementedYet|TODO", text):
        raise ValueError("unsupported or assumed extraction")
    definitions = re.findall(r"^Definition (\w+)", text, re.M)
    if definitions != ["fq_addcarryx_u32"]:
        raise ValueError("unexpected extraction boundary")
    for operation, count in {"f_add": 2, "f_bitand": 1, "f_shr": 1, "cast": 5}.items():
        if len(re.findall(r"\b" + operation + r"\b", text)) != count:
            raise ValueError("extracted operations no longer match the safety obligations")


def validate_assumptions(text):
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    if lines != ["Closed under the global context"] * len(ROOTS):
        raise ValueError("theorem assumptions are not closed")


def validate_proof_rejection(text):
    if "Carry.v" not in text or not re.search(
            r"Error: (Found no subterm matching|Unable to unify|Tactic failure)", text):
        raise ValueError("mutation failed outside theorem checking")


def shift_mutation(source):
    old = "let x3: FqU1 = ((x1 >> 32) as FqU1);"
    if source.count(old) != 1:
        raise ValueError("shift mutation no longer matches the pinned source")
    return source.replace(old, "let x3: FqU1 = ((x1 >> 33) as FqU1);")


def main():
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-proof"
        if work.exists():
            shutil.rmtree(work)
        work.mkdir(parents=True)
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "scope": "Rust Fq32 addcarry only", "theorem_roots": ROOTS, "commands": []}
        env = dict(os.environ, CARGO_BUILD_JOBS="2", RAYON_NUM_THREADS="2",
                   CARGO_TARGET_DIR=str(formal.CACHE / "decaf-proof-target"))

        def command(args, cwd=work, expect_failure=False):
            index = len(report["commands"])
            report["commands"].append(list(map(str, args)))
            log = work / f"{index:02}.log"
            failed = False
            try:
                bounded_run(list(map(str, args)), cwd, env, log, work / "unused", work, 300)
            except RuntimeError as error:
                if not expect_failure or not re.search(r"verification process failed \((1|101)\)", str(error)):
                    raise
                failed = True
            if failed != expect_failure:
                raise RuntimeError(f"unexpected command status; see {index:02}.log")
            return log.read_text()

        try:
            config = json.loads(CONFIG.read_text())
            report["toolchain"] = config
            report["runner_sha256"] = formal.file_digest(Path(__file__))
            hax_prefix = ["opam", "exec", "--switch=hax-0.3.7", "--"]
            hax_version = command([*hax_prefix, "cargo", "hax", "--version"])
            if "version=" + config["hax"]["version"] not in hax_version:
                raise ValueError("unexpected hax version")
            for tool, digest in config["hax"]["binary_sha256"].items():
                path = Path(command([*hax_prefix, "which", tool]).strip())
                if formal.file_digest(path) != digest:
                    raise ValueError(f"unrecognized hax artifact: {tool}")
            rust_version = command(["rustup", "run", config["hax"]["rust"], "rustc", "-Vv"])
            if config["hax"]["rust_commit"] not in rust_version or config["hax"]["binary_host"] not in rust_version:
                raise ValueError("unexpected hax Rust compiler")
            report["rust_test_version"] = command(["rustup", "run", config["rust_test"], "rustc", "-Vv"])
            inputs = json.loads((ROOT / "decaf/inputs.json").read_text())
            rust = inputs["libraries"]["rust"]
            report["library_revision"] = rust["candidate"]
            mirror = formal.CACHE / "decaf-rust.git"
            if not mirror.exists():
                mirror.parent.mkdir(parents=True, exist_ok=True)
                command(["git", "init", "--bare", mirror])
            command(["git", "--git-dir", mirror, "fetch", "--depth=1", rust["repository"], rust["candidate"]])
            source = command(["git", "--git-dir", mirror, "show", f"{rust['candidate']}:{SOURCE}"])
            source_path = work / "fiat-original.rs"
            source_path.write_text(source)
            report["source_sha256"] = formal.file_digest(source_path)
            support = work / "support"
            shutil.copytree(ROOT / "decaf/proofs/rocq", support,
                            ignore=shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux"))
            report["support_hashes"] = {p.name: formal.file_digest(p) for p in support.glob("*.v")}
            records = formal.CACHE / "record-update/src"
            if command(["git", "rev-parse", "HEAD"], records.parent).strip() != config["record_update"]["revision"]:
                raise ValueError("unexpected record-update revision")
            command(["git", "diff", "--exit-code", "HEAD", "--", "src"], records.parent)
            rocq = ["opam", "exec", "--switch=decaf-fv", "--", "rocq"]
            version = command([*rocq, "--version"])
            if "version " + config["rocq-runtime"] not in version:
                raise ValueError("unexpected Rocq version")
            command([*rocq, "compile", "-Q", records, "RecordUpdate", records / "RecordEta.v"])
            command([*rocq, "compile", "-Q", records, "RecordUpdate", records / "RecordSet.v"])
            for mutation in (False, True):
                case = work / ("wrong-shift" if mutation else "original")
                case.mkdir()
                case_support = case / "support"
                shutil.copytree(support, case_support)
                flags = ["-w", "-deprecated", "-Q", case_support, "Core", "-Q", records, "RecordUpdate"]
                command([*rocq, "compile", *flags, case_support / "Core.v"])
                (case / "Cargo.toml").write_text('[package]\nname="decaf_proof_slice"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
                (case / "lib.rs").write_text('''#![no_std]
pub mod fiat;
#[cfg(test)] mod tests {
    #[test] fn carry_witness() {
        let (mut lo, mut hi) = (0, 0);
        super::fiat::fq_addcarryx_u32(&mut lo, &mut hi, 1, u32::MAX, 0);
        assert_eq!((lo, hi), (0, 1));
    }
}
''')
                (case / "fiat.rs").write_text(shift_mutation(source) if mutation else source)
                witness = command(["cargo", "+" + config["rust_test"], "test", "--release", "--", "--test-threads=2"], case, expect_failure=mutation)
                if mutation and "tests::carry_witness ... FAILED" not in witness:
                    raise ValueError("mutation did not fail its arithmetic witness")
                command(["opam", "exec", "--switch=hax-0.3.7", "--", "cargo", "hax", "into", "-i",
                         "-** +decaf_proof_slice::fiat::fq_addcarryx_u32", "coq"], case)
                extraction = case / "proofs/coq/extraction"
                extracted = extraction / "Decaf_proof_slice_Fiat.v"
                validate_extraction(extracted.read_text())
                case_flags = [*flags, "-Q", extraction, "Slice"]
                command([*rocq, "compile", *case_flags, extracted])
                # Every case recompiles the authored theorem against its own fresh extraction.
                proof_log = command([*rocq, "compile", *case_flags, case_support / "Carry.v"], expect_failure=mutation)
                if mutation:
                    validate_proof_rejection(proof_log)
                if not mutation:
                    command([*rocq, "check", "-silent", "-Q", case_support, "Core", "-Q", records,
                             "RecordUpdate", "-Q", extraction, "Slice", "Core.Carry"])
                    audit = case_support / "Audit.v"
                    audit.write_text("From Core Require Import Carry.\n" + "\n".join(
                        f"Print Assumptions {root}." for root in ROOTS) + "\n")
                    validate_assumptions(command([*rocq, "compile", *case_flags, audit]))
                    report["extraction_sha256"] = formal.file_digest(extracted)
            report.update(status="passed", completed=True)
        except Exception as error:
            report["detail"] = str(error)
        finally:
            (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"status": report["status"], "report": str(work / "report.json")}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
