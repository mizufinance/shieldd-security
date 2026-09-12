#!/usr/bin/env python3
"""Replay native Rust Fq addition, helper arithmetic, and array-access proofs."""
import json
import os
from pathlib import Path
import re
import shutil

import formal
from security import bounded_run

ROOT = formal.ROOT
PROOFS = ROOT / "decaf/proofs"
MODULES = ("Core", "Carry", "RustBorrow", "RustMultiply", "RustSelect", "RustArray", "RustFieldAdd")
ROOTS = tuple("Core." + name for name in (
    "Carry.addcarry_exact", "Carry.addcarry_safety", "Carry.addcarry_reconstruction",
    "RustBorrow.borrow_exact", "RustBorrow.borrow_safety", "RustBorrow.borrow_reconstruction",
    "RustMultiply.multiply_exact", "RustMultiply.multiply_safety", "RustMultiply.multiply_reconstruction",
    "RustSelect.select_exact", "RustSelect.select_safety", "RustArray.update_length",
    "RustFieldAdd.add_correct", "RustFieldAdd.add_accesses"))


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


def validate_assumptions(text):
    if [s.strip() for s in text.splitlines() if s.strip()] != [
            "Closed under the global context"] * len(ROOTS):
        raise ValueError("native field theorem assumptions are not closed")


def validate_rejection(text):
    if "RustFieldAdd.v" not in text or not re.search(r"Error: Tactic failure:.*Cannot find witness", text, re.S):
        raise ValueError("mutation failed outside field arithmetic checking")


def main():
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-field-proof-replay"
        work.mkdir(parents=True, exist_ok=True)
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "scope": "Rust32 Fq addition and native arithmetic helpers on 64-bit targets",
                  "theorem_roots": ROOTS, "commands": [], "cases": {}}
        report_path = work / "report.json"
        report_path.write_text(json.dumps(report, indent=2) + "\n")
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
            generated = formal.WORK / "decaf-fields"
            receipt_path = generated / "report.json"
            receipt = json.loads(receipt_path.read_text())
            if receipt.get("status") != "generated" or receipt.get("completed") is not True:
                raise ValueError("native generation is incomplete")
            if receipt["fiat_revision"] != config["fiat"]["revision"] or receipt["generator_sha256"] != config["fiat"]["native_build"]["binary_sha256"]:
                raise ValueError("native generation uses an unrecognized toolchain")
            entry, = [e for e in receipt["outputs"] if e["path"] == "rust/fq.rs"]
            source_path = generated / "rust/fq.rs"
            if formal.file_digest(source_path) != entry["sha256"] or entry["command"][-3:] != ["fq", "32", config["fields"]["fq"]]:
                raise ValueError("native source does not match the shared field parameters")
            report["generation_receipt_sha256"] = formal.file_digest(receipt_path)
            source = source_path.read_text()
            hax = ["opam", "exec", "--switch=hax-0.3.7", "--"]
            for tool, digest in config["hax"]["binary_sha256"].items():
                executable = Path(command([*hax, "which", tool]).strip())
                if formal.file_digest(executable) != digest:
                    raise ValueError("unrecognized hax artifact: " + tool)
            version = command(["rustup", "run", config["hax"]["rust"], "rustc", "-Vv"])
            if config["hax"]["rust_commit"] not in version or config["hax"]["binary_host"] not in version:
                raise ValueError("unexpected extraction compiler")
            env["CARGO_BUILD_TARGET"] = config["hax"]["binary_host"]
            report["rust_test_version"] = command(["rustup", "run", config["rust_test"], "rustc", "-Vv"])
            rocq = ["opam", "exec", "--switch=decaf-fv", "--", "rocq"]
            installed = command(["opam", "list", "--switch=decaf-fv", "--installed", "--columns=version", "--short", "rocq-runtime"]).strip()
            if installed != config["rocq-runtime"]:
                raise ValueError("unexpected Rocq version")
            records = formal.CACHE / "record-update/src"
            if command(["git", "rev-parse", "HEAD"], records.parent).strip() != config["record_update"]["revision"]:
                raise ValueError("unexpected record-update revision")
            command(["git", "diff", "--exit-code", "HEAD", "--", "src"], records.parent)
            for name in ("RecordEta", "RecordSet"):
                command([*rocq, "compile", "-Q", records, "RecordUpdate", records / (name + ".v")])
            report["proof_hashes"] = {name: formal.file_digest(PROOFS / "rocq" / (name + ".v")) for name in MODULES}
            modulus = int(config["fields"]["fq"])
            limbs = [(modulus - 1 >> (32*i)) & ((1 << 32)-1) for i in range(8)]
            for mutation in (False, True):
                case = work / ("wrong-modulus" if mutation else "original")
                case.mkdir()
                (case / "Cargo.toml").write_text('[package]\nname="decaf_proof_slice"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
                (case / "fiat.rs").write_text(modulus_mutation(source) if mutation else source)
                (case / "lib.rs").write_text('#![no_std]\npub mod fiat;\n#[test] fn modulus_witness() { let mut z=[0u32;8]; fiat::fq_add(&mut z,&' + str(limbs) + ',&[1,0,0,0,0,0,0,0]); assert_eq!(z,[0u32;8]); }\n')
                report["cases"][case.name] = {"source_sha256": formal.file_digest(case / "fiat.rs")}
                witness = command(["cargo", "+" + config["rust_test"], "test", "--release", "--", "--test-threads=2"], case, mutation)
                if mutation and "modulus_witness ... FAILED" not in witness:
                    raise ValueError("mutant did not fail its native arithmetic witness")
                command([*hax, "cargo", "hax", "into", "-i", "-** +decaf_proof_slice::fiat::fq_mul +decaf_proof_slice::fiat::fq_add", "coq"], case)
                extraction = case / "proofs/coq/extraction"
                extracted = extraction / "Decaf_proof_slice_Fiat.v"
                validate_accesses(extracted.read_text())
                report["cases"][case.name]["extraction_sha256"] = formal.file_digest(extracted)
                support = case / "support"
                support.mkdir()
                flags = ["-Q", support, "Core", "-Q", records, "RecordUpdate", "-Q", extraction, "Slice"]
                for name in MODULES:
                    shutil.copyfile(PROOFS / "rocq" / (name + ".v"), support / (name + ".v"))
                command([*rocq, "compile", *flags, support / "Core.v"])
                command([*rocq, "compile", *flags, extracted])
                for name in MODULES[1:]:
                    rejected = mutation and name == "RustFieldAdd"
                    output = command([*rocq, "compile", *flags, support / (name + ".v")], expect_failure=rejected)
                    if rejected:
                        validate_rejection(output)
                if not mutation:
                    audit = support / "Audit.v"
                    audit.write_text("From Core Require Import RustFieldAdd RustMultiply.\n" + "\n".join(
                        "Print Assumptions " + root + "." for root in ROOTS) + "\n")
                    validate_assumptions(command([*rocq, "compile", *flags, audit]))
                    original_flags = flags
            command([*rocq, "check", "-silent", *original_flags, "Core.RustFieldAdd", "Core.RustMultiply"])
            report.update(status="passed", completed=True)
        except Exception as error:
            report["detail"] = str(error)
        finally:
            report_path.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
