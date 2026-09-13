#!/usr/bin/env python3
"""Replay Go reduction, multiplication and encoding for one public x86-64 state.

Run under the release Dune environment used by decaf_flow_qualify.py. This is
scoped evidence, not universal runtime, arbitrary-point or consumer coverage.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import shutil

import decaf
import formal
from decaf_inventory import MATRIX, validate

CONTROL_VARIANTS = {0: ["public", "depth"], 1: ["public"], 2: ["public"],
                    3: ["zero", "one", "public"], 4: ["timeout"], 5: ["public"]}
EXPECTED_CONTROLS = {f"{target}-{control}-{variant}-{tool}"
                     for target in ("x86_64", "aarch64")
                     for control, variants in CONTROL_VARIANTS.items() for variant in variants
                     for tool in ("original", "demand")}


def component_paths(tool):
    build = next((path for path in Path(tool).parents if path.name == "_build"), None)
    switch = os.environ.get("OPAM_SWITCH_PREFIX")
    if build is None or not switch:
        raise decaf.Blocked("qualified build and opam environments required")
    roots = [build / "install/default/lib/binsec", Path(switch) / "lib/unisim_archisec"]
    paths = {str(path) for root in roots for path in root.rglob("*")
             if path.is_file() and path.suffix in {".cmxs", ".so"}}
    if not {"binsec_sse.cmxs", "binsec_sse_checkct.cmxs", "amd64dba.cmxs", "aarch64dba.cmxs"} <= {Path(path).name for path in paths}:
        raise decaf.Blocked("required analyzer or architecture components missing")
    return paths


def validate_qualification(receipt):
    checks = receipt.get("cases", [])
    if (receipt.get("status") != "passed" or receipt.get("completed") is not True
            or len(checks) != 36 or {case["id"] for case in checks} != EXPECTED_CONTROLS
            or any(case.get("status") != "passed" for case in checks)):
        raise decaf.Blocked("complete differential decoder controls required")
    for key, name in {
        "experiment_sha256": "decaf_flow_qualify.py",
        "classifier_sha256": "decaf.py", "process_runner_sha256": "security.py",
        "source_sha256": "decaf/proofs/binary/flow-controls.c",
        "patch_sha256": "decaf/proofs/binsec-demand-decoding.patch",
    }.items():
        if receipt.get(key) != formal.file_digest(formal.ROOT / name):
            raise decaf.Blocked("stale decoder qualification: " + name)
    tool = receipt["tools"]["demand"]
    if set(tool["components"]) != component_paths(tool["path"]):
        raise decaf.Blocked("qualified component inventory is incomplete or changed")
    for entry in (tool, tool["solver"]):
        if formal.file_digest(Path(entry["path"])) != entry["sha256"]:
            raise decaf.Blocked("changed qualified analyzer or solver")
    for path, digest in tool["components"].items():
        if formal.file_digest(Path(path)) != digest:
            raise decaf.Blocked("changed qualified component: " + path)
    if Path(shutil.which("binsec") or "missing").resolve() != Path(tool["path"]).resolve():
        raise decaf.Blocked("run in the qualified release Dune environment")
    if Path(shutil.which("z3") or "missing").resolve() != Path(tool["solver"]["path"]).resolve():
        raise decaf.Blocked("qualified solver is not selected")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--purego", action="store_true")
    parser.add_argument("--runtime", choices=["pilot", "go-default-gc"], default="go-default-gc")
    args = parser.parse_args()
    with formal.exclusive_lock():
        mode = "go-encoding-" + ("purego-" if args.purego else "normal-") + args.runtime
        pilot = decaf.Pilot(mode, "go")
        pilot.work = formal.WORK / mode
        pilot.work.mkdir(exist_ok=True)
        matrix = json.loads(MATRIX.read_text())
        validate(matrix)
        source = matrix["sources"]["go"]
        pilot.inputs["libraries"]["go"].update(repository=source["repository"], candidate=source["revision"])
        pilot.env.update(GOTOOLCHAIN="go" + pilot.inputs["go"], GOOS="linux", GOARCH="amd64",
                         GOAMD64="v1", GOEXPERIMENT="", GOENV="off", GOWORK="off", CGO_ENABLED="1",
                         GOFLAGS="-p=2" + (" -tags=purego" if args.purego else ""))
        qualification_path = formal.WORK / "decaf-flow-qualification/report.json"
        pilot.report.update(
            qualification_complete=False, matrix_sha256=formal.file_digest(MATRIX),
            experiment_sha256=formal.file_digest(Path(__file__)),
            scope="scalar reduction, public-generator multiplication and compression; one initialized public Linux x86-64 snapshot",
            open_obligations=["all permitted runtime entry states and schedules", "arbitrary peer points",
                              "ARM64", "consumer intervals", "native functional refinement"],
        )

        def prerequisites(case):
            if platform.system() != "Linux" or platform.machine() != "x86_64":
                raise decaf.Blocked("native Linux x86-64 snapshot host required")
            receipt = json.loads(qualification_path.read_text())
            validate_qualification(receipt)
            case["qualification_receipt_sha256"] = formal.file_digest(qualification_path)
            case["qualification"] = receipt
            pilot.tool("go", pilot.inputs["go"])

        pilot.check("decoder-and-compiler", "tooling", prerequisites)
        if pilot.report["checks"][-1]["status"] != "passed":
            return 1

        def analyze(case):
            checkout = pilot.checkout("go", "candidate", case)
            directory = checkout / "cmd/ct-pilot"
            directory.mkdir(parents=True)
            harness = formal.ROOT / "decaf/proofs/binary/go-reduction-encoding.go"
            shutil.copyfile(harness, directory / "main.go")
            case["harness_sha256"] = formal.file_digest(harness)
            case["go_environment"] = json.loads(pilot.command(
                ["go", "env", "-json", "GOROOT", "GOVERSION", "GOOS", "GOARCH", "GOAMD64", "GOEXPERIMENT", "GOWORK", "CGO_ENABLED", "GOFLAGS", "CC", "CGO_CFLAGS", "CGO_LDFLAGS"], checkout, case))
            compiler = Path(case["go_environment"]["GOROOT"]) / "pkg/tool/linux_amd64/compile"
            case["compiler_sha256"] = formal.file_digest(compiler)
            binary = checkout / "ct-pilot"
            pilot.command(["go", "build", "-buildvcs=false", "-mod=readonly", "-p", "2", "-o", binary, "./cmd/ct-pilot"], checkout, case)
            pilot.command([binary], checkout, case, timeout=60)
            case["binary_sha256"] = formal.file_digest(binary)
            pilot.analyze(binary, case, "secure", "go", runtime_profile=args.runtime)
            if formal.file_digest(qualification_path) != pilot.report["checks"][0]["qualification_receipt_sha256"]:
                raise decaf.Blocked("qualification receipt changed during analysis")
            validate_qualification(json.loads(qualification_path.read_text()))

        pilot.check("reduction-multiplication-encoding", "compiled-trace", analyze)
        pilot.report["completed"] = True
        pilot.save()
        return 0 if pilot.report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
