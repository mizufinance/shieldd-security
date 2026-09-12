#!/usr/bin/env python3
"""Check the extracted Go Add64 implementation and a source-level shift mutant."""
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
         "GoCarry.addcarry_correct")


def shift_mutation(source):
    start = source.index("func Add64(")
    end = source.index("\n}", start) + 2
    body = source[start:end]
    if body.count(">> 63") != 1:
        raise ValueError("Add64 mutation no longer matches the source")
    return source[:start] + body.replace(">> 63", ">> 62") + source[end:]


def validate_assumptions(text):
    if [s.strip() for s in text.splitlines() if s.strip()] != [
            "Closed under the global context"] * len(ROOTS):
        raise ValueError("Go carry theorem assumptions are not closed")


def validate_rejection(text):
    if "GoCarry.v" not in text or not re.search(
            r"Error:\s+(Tactic failure|No applicable tactic|\(in proof addcarry_execution\): Attempt to save an incomplete proof)", text):
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
                  "scope": "Go Add64 functional partial correctness",
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
                     "new/golang/theory/auto.vo", "new/golang/defn.vo", "new/code/unsafe.vo"], perennial)
            goroot = Path(command(["go", "env", "GOROOT"]).strip())
            env.update(GOROOT=str(goroot), GOTOOLCHAIN="local",
                       GOMODCACHE=str(formal.CACHE / "decaf-go-modcache"),
                       PATH=str(goroot / "bin") + os.pathsep + env["PATH"])
            source_path = goroot / "src/math/bits/bits.go"
            source = source_path.read_text()
            report["go_bits_source_sha256"] = formal.file_digest(source_path)
            report["proof_hashes"] = {name: formal.file_digest(PROOFS / "rocq" / name)
                                      for name in ("CarryArithmetic.v", "GoCarryArithmetic.v", "GoCarry.v")}
            for mutation in (False, True):
                case = work / ("wrong-shift" if mutation else "original")
                case.mkdir()
                (case / "go.mod").write_text("module mizufinance.local/decaf/carrycheck\n\ngo 1.26.4\n")
                (case / "carry_test.go").write_text('''package carrycheck
import ("math/bits"; "testing")
func TestCarryWitness(t *testing.T) {
    lo, hi := bits.Add64(^uint64(0), 0, 1)
    if lo != 0 || hi != 1 { t.Fatalf("carry witness: %d %d", lo, hi) }
}
''')
                case_env = {}
                if mutation:
                    isolated = case / "goroot"
                    copy_bits_goroot(goroot, isolated)
                    (isolated / "src/math/bits/bits.go").write_text(shift_mutation(source))
                    case_env["GOROOT"] = str(isolated)
                case_source = Path(case_env.get("GOROOT", str(goroot))) / "src/math/bits/bits.go"
                report["cases"][case.name] = {"source_sha256": formal.file_digest(case_source)}
                # Disable compiler intrinsics so this witness executes the source body.
                witness = command(["go", "test", "-p", "2", "-gcflags=mizufinance.local/decaf/carrycheck=-d=ssa/intrinsics/off", "./..."],
                                  case, mutation, case_env)
                if mutation and "carry witness:" not in witness:
                    raise ValueError("mutant did not fail the executable carry witness")
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
                for name in ("CarryArithmetic.v", "GoCarryArithmetic.v"):
                    command([*rocq, "compile", *flags, support / name])
                checked = command([*rocq, "compile", *flags, support / "GoCarry.v"], expect_failure=mutation)
                if mutation:
                    validate_rejection(checked)
                else:
                    audit = support / "Audit.v"
                    audit.write_text("Require Import GoCarry.\n" + "\n".join(
                        "Print Assumptions " + root + "." for root in ROOTS) + "\n")
                    validate_assumptions(command([*rocq, "compile", *flags, audit]))
                    original_flags = flags
                    report["extraction_sha256"] = formal.file_digest(extracted)
            command([*rocq, "check", "-silent", *original_flags, "GoCarry"])
            report.update(status="passed", completed=True)
        except Exception as error:
            report["detail"] = str(error)
        finally:
            report_path.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
