#!/usr/bin/env python3
"""Replay Go Fq/Fr addition on a Linux x86-64 proof/witness host."""
import json
import hashlib
import os
from pathlib import Path
import re
import shutil
import tempfile

import formal
from decaf_go_proof import validate_assumptions
from decaf_inventory import atomic_json, MATRIX, validate
from decaf_toolchain import native_artifact
from security import bounded_run
import decaf_fiat_proof as fiat
import decaf_perennial_build as semantics
from decaf_fiat_build import build_environment

PROOFS = formal.ROOT / "decaf/proofs"
MODULES = ("CarryArithmetic", "GoCarryArithmetic", "GoCarry", "BorrowArithmetic",
           "GoBorrowArithmetic", "GoBorrow", "GoArray", "GoSelect", "GoFieldAdd", "GoFieldAliases",
           "GoFrSelect", "GoFrFieldAdd", "GoFrFieldAliases",
           "GoArrayWindows", "GoFieldOffsets", "GoFrFieldOffsets", "GoFieldPairOffsets", "GoFrFieldPairOffsets")
ROOTS = ("GoSelect.select_execution", "GoSelect.select_correct", "GoFieldAdd.add_correct") + tuple(
    "GoFieldAliases." + name for name in
    ("add_disjoint", "add_left", "add_right", "add_equal_inputs", "add_all_equal")) + (
    "GoFrSelect.select_execution", "GoFrSelect.select_correct", "GoFrFieldAdd.add_correct") + tuple(
    "GoFrFieldAliases." + name for name in
    ("add_disjoint", "add_left", "add_right", "add_equal_inputs", "add_all_equal")) + (
    "GoArrayWindows.array_append", "GoArrayWindows.array_window", "GoArrayWindows.array_window4",
    "GoFieldOffsets.add_offsets", "GoFrFieldOffsets.add_offsets") + tuple(
    module + "." + name for module in ("GoFieldPairOffsets", "GoFrFieldPairOffsets")
    for name in ("add_input_windows", "add_left_window", "add_right_window"))
CASES = (("original", None, None), ("wrong-modulus", "fq", "modulus"),
         ("wrong-fr-modulus", "fr", "modulus"), ("early-fq-write", "fq", "early-write"),
         ("early-fr-write", "fr", "early-write"))


def go_source_inventory(goroot):
    # Preserve lexical paths so adding an alias to an already bound file is
    # visible too. Content hashes alone do not detect newly introduced inputs.
    return {str(path.relative_to(goroot)): formal.file_digest(path)
            for root in (goroot / "src", goroot / "pkg/include")
            for path in sorted(root.rglob("*")) if path.is_file()}


def validate_go_sources(goroot, expected):
    if go_source_inventory(goroot) != expected:
        raise ValueError("Go source/include inventory changed")


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
    fiat.validate_generation(config, receipt, directory)


def early_write_mutation(source, field):
    if field not in {"fq", "fr"}:
        raise ValueError("unknown field")
    anchor = f"func {field.capitalize()}Add(out1 *[4]uint64, arg1 *[4]uint64, arg2 *[4]uint64) {{"
    change = anchor + "\n\tout1[0] = arg1[0]"
    if source.count(anchor) != 1 or change in source:
        raise ValueError("early-write mutation no longer matches the source")
    return source.replace(anchor, change)


def validate_field_rejection(output, proof, field="fq", path=None, kind="modulus"):
    # An infrastructure failure or an earlier execution failure is not evidence
    # that the arithmetic theorem detected the changed modulus.
    if kind == "modulus":
        lines = [i for i, line in enumerate(proof.splitlines(), 1)
                 if "split; [lia|apply Z.mod_unique" in line]
        message = "Tactic failure: Cannot find witness."
    elif kind == "early-write":
        lines = [i for i, line in enumerate(proof.splitlines(), 1)
                 if line.strip() == "array_steps. wp_func_call."][:1]
        message = "The LHS of func_unfold (# (functions _ _)) does not match any subterm of the goal"
    else:
        raise ValueError("unknown rejection stage")
    module = {"fq": "GoFieldAdd", "fr": "GoFrFieldAdd"}[field]
    expected = str(path) if path is not None else module + ".v"
    if Path(expected).name != module + ".v" or (path is not None and not Path(path).is_absolute()):
        raise ValueError("expected proof rejection path must be absolute")
    errors = re.findall(r'^File "([^"\n]+)", line (\d+), characters \d+-\d+:\s*\nError:', output, re.M)
    if (len(errors) != 1 or len(re.findall(r'^Error:', output, re.M)) != 1 or
            errors[0][0] != expected or int(errors[0][1]) not in lines or
            re.sub(r"\s+", " ", output.split("\nError:", 1)[1]).strip() != message):
        raise ValueError("mutation failed outside the field arithmetic proof")


def validate_native_rejection(output, field="fq", kind="modulus"):
    test, marker = ((f"Test{field.capitalize()}Boundary", f"{field} boundary witness:") if kind == "modulus" else
                    ("TestFieldOffsetWindows", f"{field} offsets out="))
    if kind not in {"modulus", "early-write"} or f"--- FAIL: {test} (" not in output or marker not in output:
        raise ValueError("mutation failed outside the native arithmetic witness")


def main():
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-go-field-proof-replay"
        work.mkdir(parents=True, exist_ok=True)
        report_path = work / "report.json"
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "witness_host": "x86_64-unknown-linux-gnu",
                  "scope": "Go Fq/Fr addition conditional partial correctness and all five backing-storage sharing partitions",
                  "theorem_roots": list(ROOTS), "commands": [], "cases": {},
                  "input_hashes": {}, "tools": {}, "artifacts": {}, "logs": {},
                  "kernel_reduction": "recursive checking with bytecode reduction enabled; Rocq VM/compiler correctness is trusted",
                  "open_obligations": ["concrete Go semantics and resolver interpretation",
                      "native interpretation of array addresses and permitted allocation bounds", "termination",
                      "field multiplication", "group and encoding refinement",
                      "compiled constant-time traces", "consumer and protocol refinement"]}
        atomic_json(report_path, report)
        run_root = work
        env = build_environment()
        env.update(GOMAXPROCS="1", GOFLAGS="", GOWORK="off", GOENV="off", CGO_ENABLED="0",
                   GOOS="linux", GOARCH="amd64", GOAMD64="v1", GOEXPERIMENT="",
                   GOGC="100", GODEBUG="", GOMEMLIMIT="off", OCAMLRUNPARAM="s=2M,o=20,O=50")

        def bind(path, category="artifacts"):
            path = Path(path).resolve(strict=True)
            digest = formal.file_digest(path)
            if str(path) in report[category] and report[category][str(path)] != digest:
                raise ValueError("bound artifact changed before reuse: " + str(path))
            report[category][str(path)] = digest

        def read_json(path):
            path = Path(path).resolve(strict=True)
            data = path.read_bytes()
            report["input_hashes"][str(path)] = hashlib.sha256(data).hexdigest()
            return json.loads(data)

        def copy_input(source, destination):
            shutil.copyfile(source, destination)
            if formal.file_digest(destination) != report["input_hashes"][str(source.resolve(strict=True))]:
                raise ValueError("copied source differs from frozen input: " + str(source))

        def command(args, cwd=None, reject=False, timeout=300):
            cwd = run_root if cwd is None else cwd
            log = run_root / f"{len(report['commands']):03}.log"
            args = list(map(str, args))
            report["commands"].append({"argv": args, "cwd": str(cwd), "log": str(log)})
            failed = False
            try:
                bounded_run(args, cwd, env, log, run_root / "unused", run_root, timeout)
            except RuntimeError as error:
                if not reject or not re.search(r"verification process failed \(1\)", str(error)):
                    raise
                failed = True
            finally:
                if log.is_file():
                    bind(log, "logs")
            if failed != reject:
                raise RuntimeError(f"unexpected command status; see {log.name}")
            return log.read_text()

        def check_hashes():
            for category in ("input_hashes", "tools", "artifacts", "logs"):
                for name, digest in report[category].items():
                    if formal.file_digest(Path(name)) != digest:
                        raise ValueError("changed replay input or artifact: " + name)
            actual = {str(path.resolve()) for evidence in report["cases"].values()
                      for path in Path(evidence["directory"]).rglob("*") if path.is_file() and
                      (path.suffix in {".go", ".v", ".vo", ".vos", ".vok"} or path.name in {"go.mod", "go.sum"})}
            expected = {name for name in report["artifacts"] if Path(name).suffix in
                        {".go", ".v", ".vo", ".vos", ".vok"} or Path(name).name in {"go.mod", "go.sum"}}
            if actual != expected:
                raise ValueError("missing or unrecorded source/proof artifact")

        try:
            run_root = Path(tempfile.mkdtemp(prefix="run-", dir=work)).resolve()
            report["run_root"] = str(run_root)
            config_path = PROOFS / "toolchain.json"
            config = read_json(config_path)
            runtime_path = formal.ROOT / "decaf/inputs.json"
            runtime = read_json(runtime_path)
            matrix = read_json(MATRIX)
            validate(matrix)
            generated = formal.WORK / "decaf-fields"
            receipt_path = generated / "report.json"
            receipt = read_json(receipt_path)
            build_path = formal.WORK / "decaf-perennial-build/report.json"
            build = read_json(build_path)
            fixture = PROOFS / "go-fields/field_test.go"
            for path in (config_path, runtime_path, MATRIX, receipt_path, build_path, fixture,
                         *(formal.ROOT / name for name in ("decaf_go_field_proof.py", "decaf_go_proof.py",
                             "decaf_fiat_proof.py", "decaf_fiat_build.py", "decaf_perennial_build.py",
                             "decaf_toolchain.py", "decaf_inventory.py", "formal.py", "security.py")),
                         *(PROOFS / "rocq" / (name + ".v") for name in MODULES)):
                bind(path, "input_hashes")
            validate_generation(config, receipt, generated)
            revision = matrix["sources"]["go"]["revision"]
            report["adopted_go_source"] = {"revision": revision, "files": {}}
            native_sources = {}
            for field in ("fq", "fr"):
                source_path = "internal/fiat/" + field + ".go"
                source = command(["git", "-C", formal.CACHE / "decaf-inventory/go", "show", revision + ":" + source_path])
                if source.encode() != (generated / "go" / (field + ".go")).read_bytes():
                    raise ValueError("adopted Go field differs from the proved generation")
                native_sources[field + ".go"] = source.encode()
                report["adopted_go_source"]["files"][source_path] = formal.file_digest(generated / "go" / (field + ".go"))
            semantics.validate_build(build, config)
            perennial = Path(build["source_root"]).resolve(strict=True)
            report["semantics_build_sha256"] = formal.file_digest(build_path)
            goose = (formal.CACHE / "goose").resolve(strict=True)
            goose_build = native_artifact(config, "goose")
            if formal.file_digest(goose) != goose_build["binary_sha256"]:
                raise ValueError("unrecognized Goose executable")
            bind(goose, "tools")
            report["native_host"] = goose_build["host"]
            # The extractor binary keeps its pinned build identity. Its package
            # loader and the native witnesses use the selected consumer Go runtime.
            env["GOTOOLCHAIN"] = "go" + runtime["go"]
            goroot = Path(command(["go", "env", "GOROOT"]).strip()).resolve(strict=True)
            go = (goroot / "bin/go").resolve(strict=True)
            env.update(GOROOT=str(goroot), GOTOOLCHAIN="local", GOPROXY="off", GOSUMDB="off")
            env["PATH"] = str(go.parent) + os.pathsep + env["PATH"]
            if command([go, "version"]).strip() != "go version go" + runtime["go"] + " linux/amd64":
                raise ValueError("unexpected selected Go compiler")
            bind(go, "tools")
            for name in ("compile", "link", "asm"):
                bind(goroot / "pkg/tool/linux_amd64" / name, "tools")
            report["go_sources"] = go_source_inventory(goroot)
            for relative in report["go_sources"]:
                bind(goroot / relative, "tools")
            report["environment"] = env
            prefix = ["opam", "exec", "--switch=decaf-fv", "--"]
            library = Path(build["library_root"]).resolve(strict=True)
            worker = (library / "rocq-runtime/rocqworker").resolve(strict=True)
            checker = (library.parent / "bin/rocqchk").resolve(strict=True)
            driver = (library.parent / "bin/rocq").resolve(strict=True)
            for path in (worker, checker, driver):
                if build["tools"].get(str(path)) != formal.file_digest(path):
                    raise ValueError("Rocq compiler/checker differs from the semantics build")
                bind(path, "tools")
            if command([*prefix, driver, "-v"]) != build["rocq_version"]:
                raise ValueError("Rocq version differs from the semantics build")

            def check_current():
                if Path(command(["which", "go"]).strip()).resolve(strict=True) != go:
                    raise ValueError("Go package-loader dispatch changed")
                check_hashes()
                validate_go_sources(goroot, report["go_sources"])
                validate_generation(config, receipt, generated)
                semantics.validate_build(build, config)

            for case_name, mutated_field, kind in CASES:
                mutation = mutated_field is not None
                case = run_root / case_name
                case.mkdir()
                evidence = report["cases"][case_name] = {"directory": str(case), "proof_status": "pending"}
                for name in ("fq.go", "fr.go"):
                    (case / name).write_bytes(native_sources[name])
                if mutation:
                    source = case / f"{mutated_field}.go"
                    mutator = modulus_mutation if kind == "modulus" else early_write_mutation
                    source.write_text(mutator(source.read_text(), mutated_field))
                (case / "go.mod").write_text("module mizufinance.local/decaf/fiat\n\ngo " + runtime["go"] + "\n")
                copy_input(fixture, case / "field_test.go")
                for name in ("fq.go", "fr.go", "go.mod", "field_test.go"):
                    bind(case / name)
                native = command([go, "test", "-p", "1", "-vet=off", "-count=1", "./..."], case, reject=mutation)
                if mutation:
                    validate_native_rejection(native, mutated_field, kind)
                evidence["native_status"] = ("expected arithmetic rejection" if kind == "modulus" else
                    "expected offset/frame rejection") if mutation else "passed"
                extraction, support = case / "extraction", case / "support"
                support.mkdir()
                command([goose, "-dir", case, "-out", extraction, ".", "math/bits"])
                flags = ["-Q", perennial / "src", "Perennial", "-Q", perennial / "new", "New",
                         "-Q", extraction, "New.code", "-Q", support, ""]
                extracted = extraction / "mizufinance_local/decaf/fiat.v"
                evidence["extraction_sha256"] = formal.file_digest(extracted)
                if mutation and evidence["extraction_sha256"] == report["cases"]["original"]["extraction_sha256"]:
                    raise ValueError("source mutation did not reach extraction")

                def compile_module(path, reject=False):
                    bind(path)
                    output = command([*prefix, worker, "--kind=compile", *flags, path], reject=reject)
                    if not reject and not path.with_suffix(".vo").is_file():
                        raise ValueError("missing compiled proof artifact")
                    if reject and path.with_suffix(".vo").exists():
                        raise ValueError("failed module unexpectedly produced a proof artifact")
                    for suffix in (".vo", ".vos", ".vok"):
                        artifact = path.with_suffix(suffix)
                        if artifact.is_file():
                            bind(artifact)
                    return output

                compile_module(extraction / "math/bits.v")
                compile_module(extracted)
                for module in MODULES:
                    target = support / (module + ".v")
                    copy_input(PROOFS / "rocq" / target.name, target)
                    reject = mutation and module == {"fq": "GoFieldAdd", "fr": "GoFrFieldAdd"}[mutated_field]
                    output = compile_module(target, reject=reject)
                    if reject:
                        validate_field_rejection(output, target.read_text(), mutated_field, target.resolve(), kind)
                        evidence["proof_status"] = "expected arithmetic rejection" if kind == "modulus" else "expected execution-order rejection"
                        evidence["rejected_module"] = module
                        break
                if not mutation:
                    audit = support / "Audit.v"
                    audit.write_text("Require Import " + " ".join(dict.fromkeys(root.split(".")[0] for root in ROOTS)) + ".\n" +
                                     "\n".join("Print Assumptions " + root + "." for root in ROOTS) + "\n")
                    validate_assumptions(compile_module(audit), ROOTS)
                    check_current()
                    command([*prefix, checker, "-bytecode-compiler", "yes", "-silent", *flags,
                             *MODULES, "Audit"], timeout=1800)
                    check_current()
                    evidence["proof_status"] = "compiled, closed global assumptions, recursively kernel rechecked"
                atomic_json(report_path, report)
            check_current()
            report.update(status="passed", completed=True)
        except (Exception, KeyboardInterrupt) as error:
            report.update(status="failed", completed=False, detail=str(error) or "interrupted")
        finally:
            atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
