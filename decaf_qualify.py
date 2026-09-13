#!/usr/bin/env python3
"""Exercise a candidate BINSEC installation; C controls are not library coverage."""
import argparse
import json
import os
from pathlib import Path
import re

import decaf
import formal
from decaf_inventory import MATRIX, atomic_json, validate
from security import bounded_run


def classify_control(output, number, endpoint):
    status, detail = decaf.classify_analysis(output, "secure" if number == 0 else "insecure", endpoint)
    if number and status == "passed":
        required = "control flow leak" if number == 1 else "memory access leak"
        if required not in output:
            return "blocked", "wrong leakage diagnostic for this control"
    return status, detail


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--switch", default="binsec-fv")
    parser.add_argument("--rust-fq-add", action="store_true",
                        help="also exercise the pinned Rust32 FqAdd body in a no_std harness")
    args = parser.parse_args()
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-tool-qualification"
        work.mkdir(parents=True, exist_ok=True)
        report_path = work / "report.json"
        report = {"status": "blocked", "completed": False, "full_certification": False,
                  "qualification_complete": False,
                  "scope": "C controls and optional Rust32 FqAdd, fixed public stack; no consumer/default-backend coverage",
                  "detail": "candidate tool exercise only; no library or consumer qualification",
                  "open_obligations": ["reviewed tool and loaded-component identities",
                      "actual Rust and Go binary qualification", "production consumer instruction and runtime closure",
                      "arbitrary permitted public state and nonvacuity", "native ARM64 release replay"],
                  "commands": [], "cases": []}
        atomic_json(report_path, report)
        env = dict(os.environ, OPAMROOTISOK="1", OCAMLPATH="", GIT_NO_REPLACE_OBJECTS="1",
                   CARGO_BUILD_JOBS="2", RAYON_NUM_THREADS="2")

        def command(argv, timeout=90):
            argv = list(map(str, argv))
            report["commands"].append(argv)
            log = work / f"{len(report['commands']):02}.log"
            bounded_run(argv, work, env, log, work / "unused", work, timeout)
            return log.read_text()

        try:
            matrix = json.loads(MATRIX.read_text())
            validate(matrix)
            report["matrix_sha256"] = formal.file_digest(MATRIX)
            report["runner_sha256"] = formal.file_digest(Path(__file__))
            report["classifier_sha256"] = formal.file_digest(formal.ROOT / "decaf.py")
            report["process_runner_sha256"] = formal.file_digest(formal.ROOT / "security.py")
            report["source_sha256"] = formal.file_digest(formal.ROOT / "decaf/controls.c")
            prefix = ["opam", "exec", "--switch=" + args.switch, "--"]
            tool = Path(command([*prefix, "which", "binsec"]).strip()).resolve(strict=True)
            solver = Path(command([*prefix, "which", "z3"]).strip()).resolve(strict=True)
            report["candidate_tools"] = {
                "binsec": {"path": str(tool), "sha256": formal.file_digest(tool),
                           "version": command([*prefix, tool, "-version"]).strip()},
                "z3": {"path": str(solver), "sha256": formal.file_digest(solver),
                       "version": command([*prefix, solver, "--version"]).strip()}}
            installation = Path(command(["opam", "var", "--switch=" + args.switch, "prefix"]).strip())
            report["candidate_components"] = {
                str(path.relative_to(installation)): formal.file_digest(path)
                for package in ("binsec", "unisim_archisec")
                for path in sorted((installation / "lib" / package).rglob("*"))
                if path.is_file() and path.suffix in {".cmxs", ".so"}}
            report["component_note"] = "candidate installed components, not an attestation of actual dynamic loading"
            for target in matrix["targets"]:
                compiler_name, nm_name = {
                    "x86_64-unknown-linux-gnu": ("gcc", "nm"),
                    "aarch64-unknown-linux-gnu": ("aarch64-linux-gnu-gcc", "aarch64-linux-gnu-nm")}[target]
                compiler = Path(command(["which", compiler_name]).strip()).resolve(strict=True)
                nm = Path(command(["which", nm_name]).strip()).resolve(strict=True)
                for number in range(3):
                    name = f"{target}-{number}"
                    case = {"id": name, "status": "blocked", "target": target,
                            "compiler_sha256": formal.file_digest(compiler),
                            "nm_sha256": formal.file_digest(nm)}
                    report["cases"].append(case)
                    atomic_json(report_path, report)
                    binary, cfg = work / name, work / (name + ".cfg")
                    binary.unlink(missing_ok=True)
                    command([compiler, "-O0", "-g", "-fno-pie", "-no-pie", f"-DCONTROL={number}",
                             formal.ROOT / "decaf/controls.c", "-o", binary])
                    if binary.is_symlink() or not binary.is_file():
                        raise ValueError("compiler did not produce a fresh regular binary")
                    symbols = command([nm, "-n", binary])
                    endpoints = re.findall(r"^([0-9a-f]+) T decaf_done$", symbols, re.M)
                    if len(endpoints) != 1:
                        raise ValueError("missing or ambiguous output boundary")
                    endpoint = int(endpoints[0], 16)
                    text = ("starting from <decaf_entry>\nwith concrete stack pointer\n"
                            "secret global decaf_secret\npublic global table\n"
                            f"reach 0x{endpoint:x}\nhalt at 0x{endpoint:x}\nexplore all\n")
                    decaf.validate_analysis_config(text)
                    cfg.write_text(text)
                    case.update(binary_sha256=formal.file_digest(binary), config_sha256=formal.file_digest(cfg))
                    # Keep exploring after a leak: even negative controls must
                    # reject incomplete exploration and later lifter errors.
                    output = command([*prefix, tool, "-sse", "-checkct", "-checkct-leak-info", "instr",
                                      "-smt-solver", "z3", "-sse-script", cfg, "-sse-depth", "100000",
                                      "-sse-timeout", "60", binary])
                    case["status"], case["detail"] = classify_control(output, number, endpoint)
                    atomic_json(report_path, report)
            if args.rust_fq_add:
                if not all(case["status"] == "passed" for case in report["cases"]):
                    raise ValueError("architecture controls must pass before Rust qualification")
                source = matrix["sources"]["rust"]
                source_path = "src/fields/fq/u32/fiat.rs"
                native = command(["git", "--git-dir=" + str(formal.CACHE / "decaf-rust.git"),
                                  "show", source["revision"] + ":" + source_path])
                fiat = work / "fiat.rs"
                fiat.write_text(native)
                git_prefix = ["git", "--git-dir=" + str(formal.CACHE / "decaf-rust.git")]
                blob = command([*git_prefix, "rev-parse", source["revision"] + ":" + source_path]).strip()
                if command(["git", "hash-object", "--no-filters", fiat]).strip() != blob:
                    raise ValueError("copied Rust source bytes differ from the pinned Git blob")
                harness = formal.ROOT / "decaf/proofs/binary/rust-fq-add.rs"
                main_rs = work / "main.rs"
                main_rs.write_bytes(harness.read_bytes())
                proof_tools = json.loads((formal.ROOT / "decaf/proofs/toolchain.json").read_text())
                report["proof_toolchain_sha256"] = formal.file_digest(formal.ROOT / "decaf/proofs/toolchain.json")
                rust_version = proof_tools["rust_test"]
                report["rust_compiler"] = command(["rustup", "run", rust_version, "rustc", "-Vv"])
                report["rust_source"] = {**source, "path": source_path, "git_blob": blob, "sha256": formal.file_digest(fiat),
                                         "harness_sha256": formal.file_digest(harness)}
                for target in matrix["targets"]:
                    linker = "gcc" if target.startswith("x86_64-") else "aarch64-linux-gnu-gcc"
                    binary, cfg = work / ("rust-fq-add-" + target), work / ("rust-fq-add-" + target + ".cfg")
                    case = {"id": "rust-fq-add-" + target, "status": "blocked", "target": target,
                            "scope": "unaltered pinned Rust32 FqAdd; independent 512-bit input; fixed public stack"}
                    report["cases"].append(case)
                    atomic_json(report_path, report)
                    binary.unlink(missing_ok=True)
                    command(["rustup", "run", rust_version, "rustc", "--edition=2021", "--target", target,
                             "-C", "opt-level=3", "-C", "panic=abort", "-C", "relocation-model=static",
                             "-C", "linker=" + linker, "-C", "link-arg=-nostartfiles", main_rs, "-o", binary], 120)
                    if binary.is_symlink() or not binary.is_file():
                        raise ValueError("Rust compiler did not produce a fresh regular binary")
                    symbols = command(["nm", "-n", binary])
                    def address(name, kind):
                        matches = re.findall(r"^([0-9a-f]+) " + kind + " " + name + "$", symbols, re.M)
                        if len(matches) != 1:
                            raise ValueError("missing or ambiguous Rust harness symbol: " + name)
                        return int(matches[0], 16)
                    endpoint, secret = address("decaf_done", "T"), address("decaf_secret", "B")
                    text = ("starting from <decaf_entry>\nwith concrete stack pointer\n"
                            f"@[0x{secret:x}, 64] := secret\nreach 0x{endpoint:x}\nhalt at 0x{endpoint:x}\nexplore all\n")
                    decaf.validate_analysis_config(text)
                    cfg.write_text(text)
                    case.update(binary_sha256=formal.file_digest(binary), config_sha256=formal.file_digest(cfg))
                    output = command([*prefix, tool, "-sse", "-checkct", "-checkct-leak-info", "instr",
                                      "-smt-solver", "z3", "-sse-script", cfg, "-sse-depth", "1000000",
                                      "-sse-timeout", "120", binary], 150)
                    case["status"], case["detail"] = classify_control(output, 0, endpoint)
                    atomic_json(report_path, report)
            report["completed"] = True
            expected_cases = 8 if args.rust_fq_add else 6
            if len(report["cases"]) == expected_cases and all(case["status"] == "passed" for case in report["cases"]):
                report["status"] = "passed"
        except (Exception, KeyboardInterrupt) as error:
            report["detail"] = str(error) or "qualification interrupted"
        finally:
            atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "qualification_complete": False, "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
