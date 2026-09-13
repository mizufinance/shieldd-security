#!/usr/bin/env python3
"""Replay Go Fq/Fr addition against fresh extraction and independent mutants."""
import json
import os
from pathlib import Path
import re
import shutil

import formal
from decaf_go_proof import validate_assumptions
from decaf_toolchain import native_artifact
from security import bounded_run

PROOFS = formal.ROOT / "decaf/proofs"
MODULES = ("CarryArithmetic", "GoCarryArithmetic", "GoCarry", "BorrowArithmetic",
           "GoBorrowArithmetic", "GoBorrow", "GoArray", "GoSelect", "GoFieldAdd", "GoFieldAliases",
           "GoFrSelect", "GoFrFieldAdd")
ROOTS = ("GoSelect.select_execution", "GoSelect.select_correct", "GoFieldAdd.add_correct") + tuple(
    "GoFieldAliases." + name for name in
    ("add_disjoint", "add_left", "add_right", "add_equal_inputs", "add_all_equal")) + (
    "GoFrSelect.select_execution", "GoFrSelect.select_correct", "GoFrFieldAdd.add_correct")


def modulus_mutation(source, field="fq"):
    old, new = {"fq": ("0xa11800000000001", "0xa11800000000002"),
                "fr": ("0xb95aee9ac33fd9ff", "0xb95aee9ac33fda00")}[field]
    start = source.index(f"func {field.capitalize()}Add(")
    end = source.index("\n}", start) + 2
    body = source[start:end]
    if body.count(old) != 1:
        raise ValueError(f"{field.capitalize()}Add modulus mutation no longer matches")
    return source[:start] + body.replace(old, new) + source[end:]


def validate_generation(config, receipt, directory):
    build = native_artifact(config, "fiat")
    if receipt.get("status") != "generated" or receipt.get("completed") is not True:
        raise ValueError("native generation is incomplete")
    if receipt.get("native_host", "aarch64-apple-darwin") != build["host"]:
        raise ValueError("generation host does not match")
    if (receipt.get("fiat_revision") != config["fiat"]["revision"] or
            receipt.get("generator_sha256") != build["binary_sha256"] or
            receipt.get("generator_patch_sha256") != build["printer_patch_sha256"]):
        raise ValueError("unrecognized generation toolchain")
    for field in ("fq", "fr"):
        entries = [e for e in receipt.get("outputs", []) if e.get("path") == f"go/{field}.go"]
        if len(entries) != 1:
            raise ValueError("missing or duplicate native field output")
        entry = entries[0]
        if (entry.get("command", [])[-3:] != [field, "64", config["fields"][field]] or
                formal.file_digest(directory / "go" / f"{field}.go") != entry.get("sha256")):
            raise ValueError("native source does not match the field parameters and receipt")


def validate_field_rejection(output, proof, field="fq"):
    # An infrastructure failure or an earlier execution failure is not evidence
    # that the arithmetic theorem detected the changed modulus.
    lines = [i for i, line in enumerate(proof.splitlines(), 1)
             if "split; [lia|apply Z.mod_unique" in line]
    module = {"fq": "GoFieldAdd", "fr": "GoFrFieldAdd"}[field]
    if not any(re.search(module + r'\.v", line ' + str(i) +
                         r', characters \d+-\d+:\s+Error: Tactic failure:  Cannot find witness\.', output)
               for i in lines):
        raise ValueError("mutation failed outside the field arithmetic proof")


def validate_native_rejection(output, field="fq"):
    if (f"--- FAIL: Test{field.capitalize()}Boundary (" not in output or
            f"{field} boundary witness:" not in output):
        raise ValueError("mutation failed outside the native arithmetic witness")


def main():
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-go-field-proof-replay"
        work.mkdir(parents=True, exist_ok=True)
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "scope": "Go Fq/Fr addition functional partial correctness; Fq alias corollaries",
                  "theorem_roots": ROOTS, "commands": [], "cases": {},
                  "open_obligations": ["concrete Go semantics and resolver interpretation",
                      "general offset-overlap refinement", "termination", "Fr alias corollaries",
                      "field multiplication", "group and encoding refinement",
                      "compiled constant-time traces", "consumer and protocol refinement"]}
        report_path = work / "report.json"
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        env = dict(os.environ, GOMAXPROCS="2", GOTOOLCHAIN="go1.26.4", GOFLAGS="", GOWORK="off")

        def command(args, cwd=work, reject=False):
            log = work / f"{len(report['commands']):02}.log"
            report["commands"].append(list(map(str, args)))
            failed = False
            try:
                bounded_run(list(map(str, args)), cwd, env, log, work / "unused", work, 300)
            except RuntimeError as error:
                if not reject or not re.search(r"verification process failed \(1\)", str(error)):
                    raise
                failed = True
            if failed != reject:
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
            report["toolchain_selector_sha256"] = formal.file_digest(formal.ROOT / "decaf_toolchain.py")
            report["assumption_validator_sha256"] = formal.file_digest(formal.ROOT / "decaf_go_proof.py")
            generated = formal.WORK / "decaf-fields"
            receipt_path = generated / "report.json"
            receipt = json.loads(receipt_path.read_text())
            validate_generation(config, receipt, generated)
            report["generation_receipt_sha256"] = formal.file_digest(receipt_path)
            perennial = formal.CACHE / "perennial"
            patch = PROOFS / "perennial-native.patch"
            if (command(["git", "rev-parse", "HEAD"], perennial).strip() != config["perennial"]["revision"] or
                    formal.file_digest(patch) != config["perennial"]["patch_sha256"] or
                    command(["git", "diff", "--binary", "--abbrev=7", "HEAD"], perennial) != patch.read_text()):
                raise ValueError("Perennial source does not match the reviewed revision and patch")
            goose = formal.CACHE / "goose"
            build = native_artifact(config, "goose")
            report["native_host"] = build["host"]
            if formal.file_digest(goose) != build["binary_sha256"]:
                raise ValueError("unrecognized Goose executable")
            env["GOTOOLCHAIN"] = config["goose_go"]
            if config["goose_go"] not in command(["go", "version"]):
                raise ValueError("unexpected Go toolchain")
            rocq = ["opam", "exec", "--switch=decaf-fv", "--", "rocq"]
            if command(["opam", "list", "--switch=decaf-fv", "--installed", "--columns=version",
                        "--short", "rocq-runtime"]).strip() != config["rocq-runtime"]:
                raise ValueError("unexpected Rocq version")
            command(["opam", "exec", "--switch=decaf-fv", "--", "gmake", "-j2", "TIMED=false",
                     "new/golang/theory/auto.vo", "new/golang/theory/array.vo",
                     "new/golang/defn.vo", "new/code/unsafe.vo"], perennial)
            fixture = PROOFS / "go-fields/field_test.go"
            report["native_fixture_sha256"] = formal.file_digest(fixture)
            report["proof_hashes"] = {name: formal.file_digest(PROOFS / "rocq" / (name + ".v"))
                                      for name in MODULES}
            report["go_bits_source_sha256"] = formal.file_digest(
                Path(command(["go", "env", "GOROOT"]).strip()) / "src/math/bits/bits.go")
            for case_name, mutated_field in (("original", None), ("wrong-modulus", "fq"),
                                             ("wrong-fr-modulus", "fr")):
                mutation = mutated_field is not None
                case = work / case_name
                case.mkdir()
                for name in ("fq.go", "fr.go"):
                    shutil.copyfile(generated / "go" / name, case / name)
                if mutation:
                    source = case / f"{mutated_field}.go"
                    source.write_text(modulus_mutation(source.read_text(), mutated_field))
                (case / "go.mod").write_text("module mizufinance.local/decaf/fiat\n\ngo 1.26.4\n")
                shutil.copyfile(fixture, case / "field_test.go")
                evidence = report["cases"][case_name] = {
                    "source_hashes": {name: formal.file_digest(case / name) for name in ("fq.go", "fr.go")}}
                native = command(["go", "test", "-p", "2", "-count=1", "./..."], case, reject=mutation)
                if mutation:
                    validate_native_rejection(native, mutated_field)
                evidence["native_status"] = "expected arithmetic rejection" if mutation else "passed"
                extraction, support = case / "extraction", case / "support"
                support.mkdir()
                command([goose, "-dir", case, "-out", extraction, ".", "math/bits"])
                flags = ["-Q", perennial / "src", "Perennial", "-Q", perennial / "new", "New",
                         "-Q", extraction, "New.code", "-Q", support, ""]
                extracted = extraction / "mizufinance_local/decaf/fiat.v"
                evidence["extraction_sha256"] = formal.file_digest(extracted)
                evidence["math_bits_extraction_sha256"] = formal.file_digest(extraction / "math/bits.v")
                if mutation and evidence["extraction_sha256"] == report["cases"]["original"]["extraction_sha256"]:
                    raise ValueError("source mutation did not reach extraction")
                command([*rocq, "compile", *flags, extraction / "math/bits.v"])
                command([*rocq, "compile", *flags, extracted])
                for module in MODULES:
                    target = support / (module + ".v")
                    shutil.copyfile(PROOFS / "rocq" / target.name, target)
                    reject = mutation and module == {"fq": "GoFieldAdd", "fr": "GoFrFieldAdd"}[mutated_field]
                    checked = command([*rocq, "compile", *flags, target], reject=reject)
                    if reject:
                        validate_field_rejection(checked, target.read_text(), mutated_field)
                        evidence["proof_status"] = "expected arithmetic rejection"
                        break
                if not mutation:
                    audit = support / "Audit.v"
                    audit.write_text("Require Import GoSelect GoFieldAdd GoFieldAliases GoFrSelect GoFrFieldAdd.\n" + "\n".join(
                        "Print Assumptions " + root + "." for root in ROOTS) + "\n")
                    validate_assumptions(command([*rocq, "compile", *flags, audit]), ROOTS)
                    command([*rocq, "check", "-silent", *flags,
                             "GoSelect", "GoFieldAdd", "GoFieldAliases", "GoFrSelect", "GoFrFieldAdd"])
                    evidence["proof_status"] = "compiled, closed global assumptions, kernel rechecked"
            report.update(status="passed", completed=True)
        except Exception as error:
            report["detail"] = str(error)
        finally:
            report_path.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
