#!/usr/bin/env python3
"""Generate the native Decaf field candidates from the shared Fiat parameters."""
import json
import os
from pathlib import Path
import shutil
import subprocess

import formal
from security import bounded_run


def check_native(config, work):
    rust = ['pub mod fq; pub mod fr; #[test] fn arithmetic_vectors() {']
    go = ['package fiat', 'import "testing"', 'func TestArithmeticVectors(t *testing.T) {']
    count = 0
    for field, modulus_text in config["fields"].items():
        modulus = int(modulus_text)
        values = [0, 1, modulus - 1, modulus // 2, (1 << 32) - 1, (1 << 64) - 1]
        prefix = field.capitalize()
        for x in values:
            for y in values:
                x_bytes, y_bytes = (list(v.to_bytes(32, "little")) for v in (x, y))
                rust.append('{ let xb = ' + str(x_bytes) + '; let yb = ' + str(y_bytes) + ';')
                rust.append(f'let (mut x, mut y, mut xm, mut ym, mut z, mut plain) = ([0u32;8],[0u32;8],[0u32;8],[0u32;8],[0u32;8],[0u32;8]); let mut bytes = [0u8;32]; {field}::{field}_from_bytes(&mut x,&xb); {field}::{field}_from_bytes(&mut y,&yb); {field}::{field}_to_montgomery(&mut xm,&x); {field}::{field}_to_montgomery(&mut ym,&y);')
                go.append('{ xb := [32]byte{' + ','.join(map(str, x_bytes)) + '}; yb := [32]byte{' + ','.join(map(str, y_bytes)) + '};')
                go.append(f'var x,y,xm,ym,z,plain [4]uint64; var bytes [32]byte; {prefix}FromBytes(&x,&xb); {prefix}FromBytes(&y,&yb); {prefix}ToMontgomery(&xm,&x); {prefix}ToMontgomery(&ym,&y);')
                for operation, expected in (("mul", x*y % modulus), ("add", (x+y) % modulus), ("sub", (x-y) % modulus)):
                    encoded = list(expected.to_bytes(32, "little"))
                    rust.append(f'{field}::{field}_{operation}(&mut z,&xm,&ym); {field}::{field}_from_montgomery(&mut plain,&z); {field}::{field}_to_bytes(&mut bytes,&plain); assert_eq!(bytes,{encoded});')
                    go.append(f'{prefix}{operation.capitalize()}(&z,&xm,&ym); {prefix}FromMontgomery(&plain,&z); {prefix}ToBytes(&bytes,&plain); if bytes != [32]byte' + '{' + ','.join(map(str, encoded)) + f'}} {{ t.Fatal("{field} {operation} vector {count}") }};')
                    count += 1
                rust.append('}')
                go.append('}')
    rust.append('}')
    go.append('}')
    (work / "rust/lib.rs").write_text('\n'.join(rust) + '\n')
    (work / "rust/Cargo.toml").write_text('[package]\nname="decaf_fields"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
    (work / "go/go.mod").write_text('module mizufinance.local/decaf/fiat\n\ngo 1.26\n')
    (work / "go/field_test.go").write_text('\n'.join(go) + '\n')
    env = dict(os.environ, CARGO_BUILD_JOBS="2", RAYON_NUM_THREADS="2", GOMAXPROCS="2",
               GOTOOLCHAIN=config["goose_go"], CARGO_TARGET_DIR=str(formal.CACHE / "decaf-proof-target"))
    bounded_run(["cargo", "+" + config["rust_test"], "test", "--release", "--", "--test-threads=2"],
                work / "rust", env, work / "rust-tests.log", work / "unused", work, 300)
    bounded_run(["go", "test", "-p", "2", "-count=1", "./..."], work / "go", env,
                work / "go-tests.log", work / "unused", work, 300)
    return {"vectors_per_language": count, "operations": ["mul", "add", "sub"], "status": "passed"}


def main():
    with formal.exclusive_lock():
        checkout = formal.CACHE / "fiat-crypto"
        work = formal.WORK / "decaf-fields"
        work.mkdir(parents=True, exist_ok=True)
        report = {"status": "failed", "completed": False, "full_certification": False, "outputs": []}
        report_path = work / "report.json"
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        try:
            for language in ("rust", "go"):
                if (work / language).exists():
                    shutil.rmtree(work / language)
            config = json.loads((formal.ROOT / "decaf/proofs/toolchain.json").read_text())
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
            if revision != config["fiat"]["revision"]:
                raise ValueError("unexpected Fiat revision")
            patch = formal.ROOT / "decaf/proofs/fiat-array-index.patch"
            actual_patch = subprocess.check_output(["git", "diff", "HEAD", "--"], cwd=checkout)
            if actual_patch != patch.read_bytes():
                raise ValueError("Fiat source differs from the pinned array-index printer patch")
            submodules = subprocess.check_output(["git", "submodule", "status", "--recursive"], cwd=checkout, text=True)
            if any(line[0] != " " for line in submodules.splitlines()):
                raise ValueError("Fiat submodules do not match the pinned source")
            binary = checkout / "src/ExtractionOCaml/fiat_crypto"
            build = config["fiat"]["native_build"]
            if formal.file_digest(binary) != build["binary_sha256"] or formal.file_digest(patch) != build["printer_patch_sha256"]:
                raise ValueError("unrecognized Fiat build or printer patch")
            report.update(fiat_revision=revision, submodules=submodules.splitlines(),
                          generator_patch_sha256=formal.file_digest(patch),
                          generator_sha256=formal.file_digest(binary),
                          runner_sha256=formal.file_digest(Path(__file__)))
            for language, width in config["representations"].items():
                for field, modulus in config["fields"].items():
                    directory = work / language
                    directory.mkdir(exist_ok=True)
                    target = directory / (field + (".rs" if language == "rust" else ".go"))
                    target.unlink(missing_ok=True)
                    flags = ["--lang", "Rust" if language == "rust" else "Go",
                             "--no-prefix-fiat", "--no-field-element-typedefs"]
                    if language == "rust":
                        flags += ["--public-type-case", "PascalCase", "--private-type-case", "PascalCase"]
                    else:
                        flags += ["--no-wide-int", "--relax-primitive-carry-to-bitwidth", "32,64",
                                  "--cmovznz-by-mul", "--package-name", "fiat",
                                  "--public-function-case", "UpperCamelCase",
                                  "--private-function-case", "camelCase",
                                  "--public-type-case", "UpperCamelCase",
                                  "--private-type-case", "camelCase"]
                    args = [str(binary.relative_to(formal.ROOT)), "word-by-word-montgomery",
                            *flags, "--output", str(target.relative_to(formal.ROOT)),
                            field, str(width), modulus]
                    bounded_run(args, formal.ROOT, dict(os.environ), directory / (field + ".log"),
                                work / "unused", work, 300)
                    if not target.is_file() or not target.stat().st_size:
                        raise ValueError("Fiat did not emit the requested source")
                    report["outputs"].append({"path": str(target.relative_to(work)), "command": args,
                                              "sha256": formal.file_digest(target)})
            report["native_checks"] = check_native(config, work)
            report.update(status="generated", completed=True)
        except Exception as error:
            report["detail"] = str(error)
        finally:
            report_path.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"status": report["status"], "report": str(work / "report.json")}))
        return 0 if report["status"] == "generated" else 1


if __name__ == "__main__":
    raise SystemExit(main())
