#!/usr/bin/env python3
"""Check the extracted Go carry, borrow and multiply implementations and source-level shift mutants."""
import json
import os
from pathlib import Path
import re
import shutil

import formal
from security import bounded_run

ROOT = formal.ROOT
PROOFS = ROOT / "decaf/proofs"
ROOTS = ("CarryArithmetic.carry_bit", "GoCarryArithmetic.addcarry_words",
         "GoCarry.addcarry_correct", "BorrowArithmetic.borrow_bit",
         "GoBorrowArithmetic.subborrow_words", "GoBorrow.subborrow_correct",
         "MultiplyArithmetic.split_product", "GoMultiplyArithmetic.multiply_words",
         "GoMultiply.multiply_correct")
ARRAY_ROOTS = tuple("GoArray." + name for name in (
    "offset_base", "offset_zero", "offset_add", "offset_null_inv",
    "allocation_returns", "allocation_progress", "allocate_uint64_array",
    "load_four", "store_four", "nil_index_panics", "invalid_index_panics")) + tuple(
    "GoArraySource." + name for name in ("local_correct", "read_write_correct",
        "copy_correct", "copy_same_correct", "alias_same_correct"))
MODULES = ("CarryArithmetic.v", "GoCarryArithmetic.v", "GoCarry.v",
           "BorrowArithmetic.v", "GoBorrowArithmetic.v", "GoBorrow.v",
           "MultiplyArithmetic.v", "GoMultiplyArithmetic.v", "GoMultiply.v")


def shift_mutation(source, function="Add64"):
    if function not in ("Add64", "Sub64", "Mul64"):
        raise ValueError("unsupported mutation target")
    start = source.index("func " + function + "(")
    end = source.index("\n}", start) + 2
    body = source[start:end]
    old, new = ("w1>>32", "w1>>31") if function == "Mul64" else (">> 63", ">> 62")
    if body.count(old) != 1:
        raise ValueError(function + " mutation no longer matches the source")
    return source[:start] + body.replace(old, new) + source[end:]


def validate_assumptions(text, roots=ROOTS):
    if [s.strip() for s in text.splitlines() if s.strip()] != [
            "Closed under the global context"] * len(roots):
        raise ValueError("Go carry theorem assumptions are not closed")


def validate_rejection(text, module="GoCarry"):
    theorem = {"GoCarry": "addcarry_execution", "GoBorrow": "subborrow_execution",
               "GoMultiply": "multiply_execution"}[module]
    if module + ".v" not in text or not re.search(
            r"Error:\s+(\(in proof " + theorem +
            r"\): Attempt to save an incomplete proof)", text):
        raise ValueError("mutation failed outside the Go execution theorem")


def copy_bits_goroot(source, destination):
    """Keep the toolchain shared; isolate only the source package under mutation."""
    for relative in ("", "src", "src/math"):
        target = destination / relative
        target.mkdir(parents=True, exist_ok=True)
        for entry in (source / relative).iterdir():
            child = Path(relative) / entry.name
            if str(child) in ("src", "src/math", "src/math/bits"):
                continue
            (destination / child).symlink_to(entry, target_is_directory=entry.is_dir())
    bits = destination / "src/math/bits"
    shutil.copytree(source / "src/math/bits", bits, copy_function=shutil.copyfile)
    for directory in [bits, *(p for p in bits.rglob("*") if p.is_dir())]:
        directory.chmod(0o755)


def main():
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-go-proof-replay"
        work.mkdir(parents=True, exist_ok=True)
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "scope": "Go Add64/Sub64/Mul64 functional partial correctness",
                  "theorem_roots": ROOTS, "extraction_target": "linux/amd64", "cases": {}, "commands": []}
        report_path = work / "report.json"
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        env = dict(os.environ, GOMAXPROCS="2", GOTOOLCHAIN="go1.26.4", GOFLAGS="", GOWORK="off")

        def command(args, cwd=work, expect_failure=False, extra_env=None):
            index = len(report["commands"])
            report["commands"].append(list(map(str, args)))
            log = work / f"{index:02}.log"
            failed = False
            try:
                bounded_run(list(map(str, args)), cwd, env | (extra_env or {}),
                            log, work / "unused", work, 300)
            except RuntimeError as error:
                if not expect_failure or not re.search(r"verification process failed \(1\)", str(error)):
                    raise
                failed = True
            if failed != expect_failure:
                raise RuntimeError(f"unexpected command status; see {log.name}")
            return log.read_bytes().decode("utf-8", errors="replace")

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
            perennial = formal.CACHE / "perennial"
            if command(["git", "rev-parse", "HEAD"], perennial).strip() != config["perennial"]["revision"]:
                raise ValueError("unexpected Perennial revision")
            patch = PROOFS / "perennial-native.patch"
            if formal.file_digest(patch) != config["perennial"]["patch_sha256"]:
                raise ValueError("unrecognized Perennial patch")
            if command(["git", "diff", "--binary", "HEAD"], perennial) != patch.read_text():
                raise ValueError("Perennial source does not match the reviewed patch")
            goose = formal.CACHE / "goose"
            if formal.file_digest(goose) != config["perennial"]["goose_sha256"]:
                raise ValueError("unrecognized Goose executable")
            if config["goose_go"] not in command(["go", "version"]):
                raise ValueError("unexpected Go toolchain")
            rocq = ["opam", "exec", "--switch=decaf-fv", "--", "rocq"]
            installed = command(["opam", "list", "--switch=decaf-fv", "--installed",
                                 "--columns=version", "--short", "rocq-runtime"]).strip()
            if installed != config["rocq-runtime"]:
                raise ValueError("unexpected Rocq version")
            command(["opam", "exec", "--switch=decaf-fv", "--", "gmake", "-j2", "TIMED=false",
                     "new/golang/theory/auto.vo", "new/golang/theory/array.vo",
                     "new/golang/defn.vo", "new/code/unsafe.vo"], perennial)
            goroot = Path(command(["go", "env", "GOROOT"]).strip())
            env.update(GOROOT=str(goroot), GOTOOLCHAIN="local",
                       GOMODCACHE=str(formal.CACHE / "decaf-go-modcache"),
                       PATH=str(goroot / "bin") + os.pathsep + env["PATH"])
            source_path = goroot / "src/math/bits/bits.go"
            source = source_path.read_text()
            report["go_bits_source_sha256"] = formal.file_digest(source_path)
            report["proof_hashes"] = {name: formal.file_digest(PROOFS / "rocq" / name)
                                      for name in MODULES}
            for case_name, target in (("original", None), ("wrong-carry", "Add64"),
                                      ("wrong-borrow", "Sub64"), ("wrong-multiply", "Mul64")):
                mutation = target is not None
                case = work / case_name
                case.mkdir()
                (case / "go.mod").write_text("module mizufinance.local/decaf/carrycheck\n\ngo 1.26.4\n")
                (case / "carry_test.go").write_text('''package carrycheck
import ("math/bits"; "testing")
func TestCarryWitness(t *testing.T) {
    lo, hi := bits.Add64(^uint64(0), 0, 1)
    if lo != 0 || hi != 1 { t.Fatalf("carry witness: %d %d", lo, hi) }
}
func TestBorrowWitness(t *testing.T) {
    lo, hi := bits.Sub64(0, 0, 1)
    if lo != ^uint64(0) || hi != 1 { t.Fatalf("borrow witness: %d %d", lo, hi) }
}
func TestMultiplyWitness(t *testing.T) {
    hi, lo := bits.Mul64(^uint64(0), ^uint64(0))
    if lo != 1 || hi != ^uint64(1) { t.Fatalf("multiply witness: %d %d", lo, hi) }
}
''')
                case_env = {}
                if mutation:
                    isolated = case / "goroot"
                    copy_bits_goroot(goroot, isolated)
                    (isolated / "src/math/bits/bits.go").write_text(shift_mutation(source, target))
                    case_env["GOROOT"] = str(isolated)
                case_source = Path(case_env.get("GOROOT", str(goroot))) / "src/math/bits/bits.go"
                report["cases"][case.name] = {"source_sha256": formal.file_digest(case_source)}
                # Disable compiler intrinsics so this witness executes the source body.
                witness = command(["go", "test", "-p", "2", "-gcflags=mizufinance.local/decaf/carrycheck=-d=ssa/intrinsics/off", "./..."],
                                  case, mutation, case_env)
                witness_label = {"Add64": "carry", "Sub64": "borrow", "Mul64": "multiply"}
                if mutation and witness_label[target] + " witness:" not in witness:
                    raise ValueError("mutant did not fail the executable arithmetic witness")
                extraction = case / "extraction"
                command([goose, "-dir", case, "-out", extraction, "math/bits"], case, extra_env=case_env)
                support = case / "support"
                support.mkdir()
                for name in report["proof_hashes"]:
                    shutil.copyfile(PROOFS / "rocq" / name, support / name)
                flags = ["-Q", perennial / "src", "Perennial", "-Q", perennial / "new", "New",
                         "-Q", extraction, "New.code", "-Q", support, ""]
                extracted = extraction / "math/bits.v"
                report["cases"][case.name]["extraction_sha256"] = formal.file_digest(extracted)
                if mutation and report["cases"][case.name]["extraction_sha256"] == report["cases"]["original"]["extraction_sha256"]:
                    raise ValueError("mutation did not reach the extracted source")
                command([*rocq, "compile", *flags, extracted])
                for name in MODULES:
                    reject = name == {"Add64": "GoCarry.v", "Sub64": "GoBorrow.v",
                                      "Mul64": "GoMultiply.v"}.get(target)
                    checked = command([*rocq, "compile", *flags, support / name], expect_failure=reject)
                    if reject:
                        validate_rejection(checked, Path(name).stem)
                        break
                if not mutation:
                    audit = support / "Audit.v"
                    audit.write_text("Require Import GoCarry GoBorrow GoMultiply.\n" + "\n".join(
                        "Print Assumptions " + root + "." for root in ROOTS) + "\n")
                    validate_assumptions(command([*rocq, "compile", *flags, audit]))
                    original_flags = flags
                    report["extraction_sha256"] = formal.file_digest(extracted)
            command([*rocq, "check", "-silent", *original_flags, "GoCarry", "GoBorrow", "GoMultiply"])
            array_case = work / "arrays"
            shutil.copytree(PROOFS / "go-arrays", array_case)
            command(["go", "test", "-p", "2", "./..."], array_case)
            extraction = array_case / "extraction"
            command([goose, "-dir", array_case, "-out", extraction, "."], array_case)
            support = array_case / "support"
            support.mkdir()
            flags = ["-Q", perennial / "src", "Perennial", "-Q", perennial / "new", "New",
                     "-Q", extraction, "New.code", "-Q", support, ""]
            extracted = extraction / "mizufinance_local/decaf/arrays.v"
            command([*rocq, "compile", *flags, extracted])
            for name in ("GoArray.v", "GoArraySource.v", "GoArrayContradiction.v"):
                shutil.copyfile(PROOFS / "rocq" / name, support / name)
            command([*rocq, "compile", *flags, support / "GoArray.v"])
            command([*rocq, "compile", *flags, support / "GoArraySource.v"])
            rejection = command([*rocq, "compile", *flags, support / "GoArrayContradiction.v"],
                                expect_failure=True)
            if not all(fragment in rejection for fragment in (
                    'The term "eq_refl"', 'go.array_offset (Loc 0 1) (-1)',
                    'cannot unify', '"null"')):
                raise ValueError("address contradiction control failed outside its false premise")
            audit = support / "ArrayAudit.v"
            audit.write_text("Require Import GoArray GoArraySource.\n" + "\n".join(
                "Print Assumptions " + root + "." for root in ARRAY_ROOTS) + "\n")
            validate_assumptions(command([*rocq, "compile", *flags, audit]), ARRAY_ROOTS)
            command([*rocq, "check", "-silent", *flags, "GoArray", "GoArraySource"])
            report["arrays"] = {
                "theorem_roots": ARRAY_ROOTS,
                "extraction_sha256": formal.file_digest(extracted),
                "source_hashes": {p.name: formal.file_digest(p) for p in
                                  sorted((PROOFS / "go-arrays").iterdir()) if p.is_file()},
                "proof_hashes": {name: formal.file_digest(support / name) for name in
                                 ("GoArray.v", "GoArraySource.v", "GoArrayContradiction.v")},
                "old_contradiction_rejected": True,
                "native_address_panics_checked": True,
                "scope": "four-word array allocation, indexing, copies, and same-array aliasing"}
            report.update(status="passed", completed=True)
        except Exception as error:
            report["detail"] = str(error)
        finally:
            report_path.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
