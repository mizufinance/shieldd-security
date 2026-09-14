#!/usr/bin/env python3
"""Build the reached Go semantics imports from fresh, exact Perennial source."""
import argparse
import json
import os
from pathlib import Path
import shlex
import tempfile

import formal
from decaf_fiat_build import build_environment, export_tree
from decaf_inventory import atomic_json
from security import bounded_run

TARGETS = ("new/golang/theory/auto.vo", "new/golang/theory/array.vo",
           "new/golang/defn.vo", "new/code/unsafe.vo")
COMPILED = {".vo", ".vos", ".vok", ".cmxs", ".cma", ".cmo", ".cmx", ".so", ".o"}
INPUTS = ("decaf_perennial_build.py", "decaf/proofs/toolchain.json", "decaf/proofs/perennial-native.patch",
          "formal.py", "security.py", "decaf_inventory.py", "decaf_fiat_build.py")


def input_hashes():
    return {str((formal.ROOT / name).resolve(strict=True)): formal.file_digest(formal.ROOT / name) for name in INPUTS}


def tool_hashes(library):
    return {str(path.resolve(strict=True)): formal.file_digest(path) for path in
            (library.parent / "bin/rocq", library.parent / "bin/rocqchk", library / "rocq-runtime/rocqworker")}


def hashes(root, predicate):
    return {str(path.relative_to(root)): formal.file_digest(path)
            for path in sorted(root.rglob("*")) if path.is_file() and predicate(path)}


def installed_hashes(library):
    runtime = library / "rocq-runtime"
    return {str(path): formal.file_digest(path)
            for path in sorted(library.rglob("*")) if path.is_file() and
            (path.suffix in {".vo", ".cmxs", ".so"} or path.parent == runtime)}


def validate_sources(report):
    root = Path(report["source_root"]).resolve(strict=True)
    for name, digest in report["source_files"].items():
        path = root / name
        if (not path.resolve().is_relative_to(root) or not path.is_file() or
                path.is_symlink() or formal.file_digest(path) != digest):
            raise ValueError("changed exported source: " + name)
    for name, target in report["source_links"].items():
        path = root / name
        if not path.is_symlink() or os.readlink(path) != target or not path.resolve().is_relative_to(root):
            raise ValueError("changed exported link: " + name)
    current = {str(path.relative_to(root)) for path in root.rglob("*.v") if path.is_file()}
    expected = {name for name in (*report["source_files"], *report["source_links"]) if name.endswith(".v")}
    if current != expected:
        raise ValueError("proof source inventory changed")


def validate_build(report, config):
    if (report.get("status") != "passed" or report.get("completed") is not True or
            report.get("full_certification") is not False or report.get("targets") != list(TARGETS) or
            report.get("revision") != config["perennial"]["revision"] or
            report.get("patch_sha256") != config["perennial"]["patch_sha256"]):
        raise ValueError("missing or mismatched Perennial build closure")
    validate_sources(report)
    root = Path(report["source_root"]).resolve(strict=True)
    library = Path(report["library_root"]).resolve(strict=True)
    if (not library.is_dir() or not report.get("installed_imports") or
            not {"Makefile", "_RocqProject", *(str(Path(name).with_suffix(".v")) for name in TARGETS)} <= report["source_files"].keys()):
        raise ValueError("empty or incomplete source/import closure")
    if (not report.get("sources") or report["sources"][0].get("revision") != config["perennial"]["revision"] or
            Path(report["sources"][0].get("destination", "")).resolve() != root):
        raise ValueError("missing or changed exact source export identity")
    if report["input_hashes"] != input_hashes():
        raise ValueError("missing or stale build input inventory")
    if report["tools"] != tool_hashes(library):
        raise ValueError("missing or stale proof tool inventory")
    if hashes(root, lambda path: path.suffix in COMPILED) != report["artifacts"]:
        raise ValueError("Perennial compiled artifact inventory changed")
    if not set(TARGETS) <= report["artifacts"].keys():
        raise ValueError("missing reached semantics imports")
    if any(str(Path(name).with_suffix(".v")) not in report["source_files"]
           for name in report["artifacts"] if name.endswith(".vo")):
        raise ValueError("compiled import lacks a bound source")
    if installed_hashes(library) != report["installed_imports"]:
        raise ValueError("installed proof import inventory changed")
    for category in ("input_hashes", "tools", "installed_imports"):
        for name, digest in report[category].items():
            if formal.file_digest(Path(name)) != digest:
                raise ValueError("changed build input/tool/import: " + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-parent", type=Path, default=Path("/root/decaf-fv-cache"))
    args = parser.parse_args()
    with formal.exclusive_lock():
        work = formal.WORK / "decaf-perennial-build"
        work.mkdir(parents=True, exist_ok=True)
        report_path = work / "report.json"
        report = {"status": "failed", "completed": False, "full_certification": False,
                  "scope": "fresh source build of reached Perennial Go semantics imports; not an inhabitance or native refinement proof",
                  "targets": list(TARGETS), "commands": [], "sources": [], "tools": {}, "installed_imports": {}}
        atomic_json(report_path, report)
        env = build_environment()
        env["OCAMLRUNPARAM"] = "s=2M,o=20,O=50"

        def command(argv, cwd=work, timeout=300):
            argv = list(map(str, argv))
            log = work / f"{len(report['commands']):03}.log"
            report["commands"].append({"argv": argv, "cwd": str(cwd), "log": str(log)})
            atomic_json(report_path, report)
            bounded_run(argv, cwd, env, log, work / "unused", work, timeout)
            return log.read_text()

        try:
            config_path = formal.ROOT / "decaf/proofs/toolchain.json"
            config = json.loads(config_path.read_text())
            patch = formal.ROOT / "decaf/proofs/perennial-native.patch"
            if formal.file_digest(patch) != config["perennial"]["patch_sha256"]:
                raise ValueError("unreviewed Perennial patch")
            report["input_hashes"] = input_hashes()
            args.build_parent.mkdir(parents=True, exist_ok=True)
            source = Path(tempfile.mkdtemp(prefix="perennial-proof-source-", dir=args.build_parent)).resolve()
            report.update(source_root=str(source), revision=config["perennial"]["revision"],
                          patch_sha256=formal.file_digest(patch))
            export_tree((formal.CACHE / "perennial").resolve(strict=True), report["revision"], source, env, report["sources"])
            env["GIT_CEILING_DIRECTORIES"] = str(source.parent)
            command(["git", "apply", "--verbose", patch], source)
            if any(path.suffix in COMPILED for path in source.rglob("*")):
                raise ValueError("source export contains precompiled artifacts")
            report["source_files"] = hashes(source, lambda path: not path.is_symlink())
            report["source_links"] = {str(path.relative_to(source)): os.readlink(path)
                                      for path in source.rglob("*") if path.is_symlink()}
            prefix = ["opam", "exec", "--switch=decaf-fv", "--"]
            for package in ("rocq-runtime", "rocq-stdlib", "coq-core", "ocaml"):
                version = command(["opam", "list", "--switch=decaf-fv", "--installed", "--columns=version", "--short", package]).strip()
                if version != config[package]:
                    raise ValueError("unexpected package: " + package)
            driver = Path(command([*prefix, "which", "rocq"]).strip()).resolve(strict=True)
            checker = Path(command([*prefix, "which", "rocqchk"]).strip()).resolve(strict=True)
            library = Path(command(["opam", "var", "--switch=decaf-fv", "lib"]).strip()).resolve(strict=True)
            worker = (library / "rocq-runtime/rocqworker").resolve(strict=True)
            for path in (driver, checker, worker):
                report["tools"][str(path)] = formal.file_digest(path)
            report["library_root"] = str(library)
            report["installed_imports"] = installed_hashes(library)
            report["rocq_version"] = command([*prefix, driver, "-v"])
            report["build_environment"] = env
            report["trust_boundary"] = "Rocq/OCaml, installed library artifacts and OS build tools; semantic contracts still require a concrete interpretation"
            command([*prefix, "gmake", "-j1", "TIMED=false", "ROCQ_C=" + shlex.join([str(worker), "--kind=compile"]), *TARGETS], source, timeout=14400)
            validate_sources(report)
            report["artifacts"] = hashes(source, lambda path: path.suffix in COMPILED)
            if not set(TARGETS) <= report["artifacts"].keys():
                raise ValueError("missing target after source build")
            report.update(status="passed", completed=True)
            validate_build(report, config)
        except (Exception, KeyboardInterrupt) as error:
            report.update(status="failed", completed=False, detail=str(error) or "interrupted")
        finally:
            atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "report": str(report_path)}))
        return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
