#!/usr/bin/env python3
"""Replay actual Go64 multiplication on ARM64 in one explicit public entry state."""
import argparse
import json
import os
from pathlib import Path
import re
import tempfile

import decaf
import formal
import decaf_fiat_proof as fiat
from decaf_inventory import MATRIX, atomic_json, validate
from security import bounded_run


CASES = ("original", "branch", "address")
MODULE = "mizufinance_local/armqual"


def harness(case):
    if case not in CASES:
        raise ValueError("unknown control")
    return f'''package main
import "{MODULE}/fiat"
var secret [8]uint64
var outputFq, outputFr [4]uint64
var table = [2]uint64{{1,2}}
//go:noinline
func decafDone() {{ _ = outputFq; _ = outputFr }}
//go:noinline
func decafEntry() {{
 {"if secret[0]&1 != 0 { decafDone(); return }" if case == "branch" else ""}
 a := [4]uint64{{secret[0],secret[1],secret[2],secret[3]}}
 b := [4]uint64{{secret[4],secret[5],secret[6],secret[7]}}
 fiat.FqMul(&outputFq,&a,&b)
 fiat.FrMul(&outputFr,&a,&b)
 {"outputFq[0] ^= table[secret[0]&1]" if case == "address" else ""}
 decafDone()
}}
func main() {{ decafEntry() }}
'''


def symbol(symbols, name):
    matches = re.findall(r"^\s*([0-9a-f]+) [TDB] " + re.escape(name) + r"$", symbols, re.M)
    if len(matches) != 1:
        raise ValueError("missing or ambiguous symbol: " + name)
    return int(matches[0], 16)


def configuration(entry, done, secret):
    if len({entry, done, secret}) != 3:
        raise ValueError("entry, output boundary and secret must differ")
    return f'''starting from 0x{entry:x}
sp<64> := 0x70000000
x28<64> := 0x71000000
@[0x71000000, 8] := 0x6fff0000
@[0x71000008, 8] := 0x70010000
@[0x71000010, 8] := 0x6fff0000
@[0x{secret:x}, 64] := secret
reach 0x{done:x}
halt at 0x{done:x}
explore all
'''


def classify(output, case, done):
    if case not in CASES:
        raise ValueError("unknown control")
    status, detail = decaf.classify_analysis(output, "secure" if case == "original" else "insecure", done)
    if status != "passed":
        raise ValueError(detail)
    # Require reached boundaries even for controls; an early leak alone is insufficient.
    reached = re.findall(r"^\[sse:result\] Path \d+ reached address (0x[0-9a-f]+)\b", output, re.M | re.I)
    if done not in map(lambda value: int(value, 16), reached):
        raise ValueError("control exploration did not reach the declared boundary")
    counts = {}
    for label in ("total paths", "completed/cut paths", "pending paths", "discontinued paths", "failed assertions"):
        values = re.findall(r"^\s*" + re.escape(label) + r"\s+(\d+)\s*$", output, re.M)
        if len(values) != 1:
            raise ValueError("missing or ambiguous exploration count: " + label)
        counts[label] = int(values[0])
    if (counts["total paths"] < 1 or counts["total paths"] != counts["completed/cut paths"] or
            any(counts[label] for label in ("pending paths", "discontinued paths", "failed assertions"))):
        raise ValueError("incomplete or failed exploration")
    if case != "original":
        expected = "control flow leak" if case == "branch" else "memory access leak"
        if expected not in output:
            raise ValueError("wrong leak diagnostic")
    return detail


def check_hashes(hashes):
    for name, digest in hashes.items():
        path = Path(name)
        if not path.is_file() or formal.file_digest(path) != digest:
            raise ValueError("changed or missing bound artifact: " + name)


def validate_parent(parent, matrix):
    expected = {f"{target}-{number}" for target in matrix["targets"] for number in range(3)}
    expected |= {"rust-fq-add-" + target for target in matrix["targets"]}
    cases = parent.get("cases", [])
    if (parent.get("status") != "passed" or parent.get("completed") is not True or
            parent.get("full_certification") is not False or parent.get("qualification_complete") is not False or
            len(cases) != len(expected) or {case.get("id") for case in cases} != expected or
            any(case.get("status") != "passed" for case in cases)):
        raise ValueError("missing candidate analyzer qualification closure")
    for key, path in {"matrix_sha256": MATRIX, "runner_sha256": formal.ROOT / "decaf_qualify.py",
                      "classifier_sha256": formal.ROOT / "decaf.py", "process_runner_sha256": formal.ROOT / "security.py",
                      "source_sha256": formal.ROOT / "decaf/controls.c",
                      "proof_toolchain_sha256": formal.ROOT / "decaf/proofs/toolchain.json"}.items():
        if parent.get(key) != formal.file_digest(path):
            raise ValueError("stale candidate qualification: " + key)
    if (parent["candidate_source"]["patch_sha256"] != formal.file_digest(formal.ROOT / "decaf/proofs/binsec-demand-decoding.patch") or
            parent["rust_source"]["harness_sha256"] != formal.file_digest(formal.ROOT / "decaf/proofs/binary/rust-fq-add.rs")):
        raise ValueError("stale candidate fixture or patch")
    if set(parent["candidate_tools"]) != {"binsec", "z3"} or not parent["candidate_components"]:
        raise ValueError("missing candidate tool/component inventory")
    directory = formal.WORK / "decaf-tool-qualification-demand"
    for case in cases:
        for suffix, key in (("", "binary_sha256"), (".cfg", "config_sha256")):
            if formal.file_digest(directory / (case["id"] + suffix)) != case.get(key):
                raise ValueError("stale candidate control artifact")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--goroot", required=True, type=Path)
    parser.add_argument("--dune-root", required=True, type=Path)
    args = parser.parse_args()
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-go-arm64-qualification"
        work.mkdir(parents=True, exist_ok=True)
        report_path = work / "report.json"
        report = {"status": "blocked", "completed": False, "full_certification": False,
                  "qualification_complete": False, "cases": {}, "commands": [],
                  "scope": "actual Go64 Fq/Fr multiplication, ARM64, independently secret 512-bit buffers, one concrete public entry state",
                  "assumptions": ["valid public goroutine/stack state with no pending preemption at entry",
                      "binary lifting and analyzer correctness", "output values disclosed at decafDone"],
                  "open_obligations": ["all permitted runtime entry states and scheduling",
                      "consumer binaries and complete instruction closure", "actual loaded-component attestation",
                      "native ARM64 execution and performance", "full matrix qualification"],
                  "input_hashes": {}, "tool_hashes": {}, "artifact_hashes": {}}
        atomic_json(report_path, report)
        env = dict(os.environ, OPAMROOTISOK="1", OCAMLPATH="", GIT_NO_REPLACE_OBJECTS="1",
                   GOROOT=str(args.goroot), GOTOOLCHAIN="local", GOOS="linux", GOARCH="arm64",
                   GOENV="off", GOWORK="off", CGO_ENABLED="0", GOFLAGS="", GOEXPERIMENT="", GOARM64="v8.0",
                   GOMAXPROCS="1", GOGC="100", GODEBUG="", GOMEMLIMIT="off")

        def bind(path, category="artifact_hashes"):
            path = Path(path).resolve(strict=True)
            report[category][str(path)] = formal.file_digest(path)

        def command(argv, cwd=work, timeout=120):
            argv = list(map(str, argv))
            log = work / f"command-{len(report['commands']):03}.log"
            report["commands"].append({"argv": argv, "cwd": str(cwd), "log": str(log)})
            bounded_run(argv, cwd, env, log, work / "unused", work, timeout)
            bind(log)
            return log.read_text()

        try:
            args.goroot = args.goroot.resolve(strict=True)
            env["GOROOT"] = str(args.goroot)
            parent_path = formal.WORK / "decaf-tool-qualification-demand/report.json"
            generation_path = formal.WORK / "decaf-fields/report.json"
            for path in (Path(__file__), MATRIX, parent_path, generation_path,
                         *(formal.ROOT / name for name in ("decaf.py", "formal.py", "security.py", "decaf_inventory.py",
                             "decaf_fiat_proof.py", "decaf_toolchain.py", "decaf/proofs/toolchain.json"))):
                bind(path, "input_hashes")
            matrix = json.loads(MATRIX.read_text())
            validate(matrix)
            parent = json.loads(parent_path.read_text())
            validate_parent(parent, matrix)
            for tool in parent["candidate_tools"].values():
                report["tool_hashes"][tool["path"]] = tool["sha256"]
            report["tool_hashes"].update(parent["candidate_components"])
            check_hashes(report["tool_hashes"])
            source_root = args.dune_root.resolve(strict=True)
            if str(source_root) != parent["candidate_source"]["path"]:
                raise ValueError("candidate source directory changed")
            modified = source_root / "src/sse/exec.ml"
            if formal.file_digest(modified) != parent["candidate_source"]["modified_source_sha256"]:
                raise ValueError("candidate analyzer patch changed")
            bind(modified, "input_hashes")
            go = args.goroot / "bin/go"
            for path in (go, *(args.goroot / "pkg/tool/linux_amd64" / name for name in ("compile", "link", "asm"))):
                bind(path, "tool_hashes")
            selected_tools = {}
            for name in ("nm", "objdump"):
                selected = Path(command([go, "tool", "-n", name]).strip()).resolve(strict=True)
                bind(selected, "tool_hashes")
                selected_tools[name] = selected
            compiler = args.goroot / "pkg/tool/linux_amd64/compile"
            if formal.file_digest(compiler) != "02f943635cc008f47a9bed37a81b82cdb28ed1c69dde34440abc8aabbc70b942":
                raise ValueError("Go compiler differs from the pinned consumer compiler")
            # Bind the runtime/standard-library build inputs, not only the driver.
            for root in (args.goroot / "src", args.goroot / "pkg/include"):
                for path in sorted(root.rglob("*")):
                    if path.is_file():
                        bind(path, "tool_hashes")
            if command([go, "version"]).strip() != "go version go1.25.4 linux/amd64":
                raise ValueError("unexpected Go toolchain")
            report["environment"] = {key: env[key] for key in ("GOROOT", "GOTOOLCHAIN", "GOOS", "GOARCH",
                "GOENV", "GOWORK", "CGO_ENABLED", "GOFLAGS", "GOEXPERIMENT", "GOARM64", "GOMAXPROCS", "GOGC", "GODEBUG", "GOMEMLIMIT")}
            generation = json.loads(generation_path.read_text())
            config = json.loads((formal.ROOT / "decaf/proofs/toolchain.json").read_text())
            fiat.validate_generation(config, generation, generation_path.parent)
            revision = matrix["sources"]["go"]["revision"]
            report["source_revision"] = revision
            analyzer = Path(parent["candidate_tools"]["binsec"]["path"])
            prefix = ["opam", "exec", "--switch=binsec-fv", "--", "dune", "exec", "--profile", "release", "--root", source_root, "--"]
            solver = Path(command([*prefix, "which", "z3"]).strip()).resolve(strict=True)
            if (str(solver) != parent["candidate_tools"]["z3"]["path"] or
                    formal.file_digest(solver) != parent["candidate_tools"]["z3"]["sha256"]):
                raise ValueError("selected solver differs from qualification")
            installation = Path(command(["opam", "var", "--switch=binsec-fv", "prefix"]).strip())
            def components():
                return {str(path): formal.file_digest(path)
                    for root, package in ((source_root / "_build/install/default", "binsec"), (installation, "unisim_archisec"))
                    for path in sorted((root / "lib" / package).rglob("*"))
                    if path.is_file() and path.suffix in {".cmxs", ".so"}}
            if components() != parent["candidate_components"]:
                raise ValueError("candidate component inventory changed")
            source_work = Path(tempfile.mkdtemp(prefix="sources-", dir=work))
            for case in CASES:
                directory = source_work / case
                (directory / "fiat").mkdir(parents=True, exist_ok=True)
                report["cases"][case] = {"status": "blocked"}
                atomic_json(report_path, report)
                for field in ("fq", "fr"):
                    text = command(["git", "-C", formal.CACHE / "decaf-inventory/go", "show",
                                    revision + ":internal/fiat/" + field + ".go"])
                    path = directory / "fiat" / (field + ".go")
                    path.write_text(text)
                    expected = [item["sha256"] for item in generation["outputs"] if item["path"] == "go/" + field + ".go"]
                    if expected != [formal.file_digest(path)]:
                        raise ValueError("adopted Go source differs from generation")
                    bind(path)
                for name, text in (("main.go", harness(case)), ("go.mod", f"module {MODULE}\n\ngo 1.25.4\n")):
                    path = directory / name
                    path.write_text(text)
                    bind(path)
                binary = directory / "field-mul-arm64"
                binary.unlink(missing_ok=True)
                command([go, "build", "-buildvcs=false", "-mod=readonly", "-p", "1", "-o", binary, "."], directory)
                bind(binary)
                symbols = command([go, "tool", "nm", binary])
                entry, done, secret = (symbol(symbols, name) for name in ("main.decafEntry", "main.decafDone", "main.secret"))
                disassembly = command([go, "tool", "objdump", "-s", "main.decafEntry|armqual/fiat.FqMul|armqual/fiat.FrMul", binary])
                if "UMULH" not in disassembly:
                    raise ValueError("actual high multiplication instruction absent")
                cfg = directory / "analysis.cfg"
                cfg.write_text(configuration(entry, done, secret))
                decaf.validate_analysis_config(cfg.read_text())
                bind(cfg)
                output = command([*prefix, analyzer, "-sse", "-checkct", "-checkct-leak-info", "instr",
                    "-smt-solver", "z3", "-sse-script", cfg, "-sse-depth", "100000", "-sse-timeout", "60", binary], directory)
                detail = classify(output, case, done)
                report["cases"][case] = {"status": "passed", "entry": entry, "done": done, "secret": secret, "detail": detail}
            for category in ("input_hashes", "tool_hashes", "artifact_hashes"):
                check_hashes(report[category])
            if Path(command([*prefix, "which", "z3"]).strip()).resolve(strict=True) != solver:
                raise ValueError("solver dispatch changed")
            for name, selected in selected_tools.items():
                if Path(command([go, "tool", "-n", name]).strip()).resolve(strict=True) != selected:
                    raise ValueError("Go tool dispatch changed: " + name)
            validate_parent(parent, matrix)
            fiat.validate_generation(config, generation, generation_path.parent)
            if components() != parent["candidate_components"]:
                raise ValueError("candidate component inventory changed during analysis")
            for category in ("input_hashes", "tool_hashes", "artifact_hashes"):
                check_hashes(report[category])
            report.update(status="passed", completed=True)
        except (Exception, KeyboardInterrupt) as error:
            report["detail"] = str(error) or "interrupted"
        finally:
            atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
