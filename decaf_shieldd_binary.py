#!/usr/bin/env python3
"""Replay one actual Shieldd KA interval; arbitrary peers/runtime states remain open."""
import argparse
import json
import os
from pathlib import Path
import platform
import re
import shutil
import tempfile

import decaf
import formal
from decaf_go_binary import validate_qualification
from decaf_inventory import CACHES, MATRIX, validate
from decaf_fiat_build import export_tree

TARGET = "x86_64-unknown-linux-gnu"
RUST = "1.90.0"
HARNESS = formal.ROOT / "decaf/proofs/binary/shieldd-key-agreement.rs"


def resolved_decaf(metadata, expected):
    packages = {p["id"]: p for p in metadata["packages"]}
    ka = [p for p in packages.values() if p["name"] == "decaf377-ka"]
    if len(ka) != 1:
        raise decaf.Blocked("ambiguous KA package")
    node = next(n for n in metadata["resolve"]["nodes"] if n["id"] == ka[0]["id"])
    deps = [d["pkg"] for d in node["deps"] if d["name"] == "decaf377"]
    if len(deps) != 1:
        raise decaf.Blocked("missing or ambiguous KA Decaf dependency")
    selected = packages[deps[0]]
    sha = expected["revision"]
    # Cargo canonicalizes the optional Git URL suffix in source identities.
    repositories = {expected["repository"], expected["repository"].removesuffix(".git")}
    if selected["source"] not in {f'git+{url}?rev={sha}#{sha}' for url in repositories}:
        raise decaf.Blocked("resolved KA Decaf dependency differs from the matrix")
    return {key: selected[key] for key in ("id", "name", "version", "source")}


def tree_state(source):
    return {str(p.relative_to(source)): {"mode": p.lstat().st_mode & 0o177777,
             "symlink": os.readlink(p) if p.is_symlink() else None,
             "sha256": formal.file_digest(p) if p.is_file() and not p.is_symlink() else None}
            for p in sorted(source.rglob("*"))}


def address_control_leaks(log, start, size):
    leaks = [int(address, 16) for address in re.findall(
        r"Instruction (0x[0-9a-f]+) has memory access leak", log)]
    matched = sorted({address for address in leaks if start <= address < start + size})
    if size <= 0 or not matched:
        raise decaf.Blocked("injected store function has no reported memory-access leak")
    return matched


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--address-control", action="store_true",
                        help="require detection of a deliberately injected secret-indexed store")
    args = parser.parse_args()
    with formal.exclusive_lock():
        mode = "shieldd-ka-native" + ("-address-control" if args.address_control else "")
        pilot = decaf.Pilot(mode, "rust")
        pilot.work = Path(tempfile.mkdtemp(prefix="shieldd-ka-native-", dir=formal.WORK))
        matrix = json.loads(MATRIX.read_text())
        validate(matrix)
        for name in ("CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
                     "RUSTC", "RUSTDOC", "CARGO_ENCODED_RUSTDOCFLAGS", "RUSTDOCFLAGS"):
            pilot.env.pop(name, None)
        pilot.env.update(RUSTUP_TOOLCHAIN=RUST, CARGO_BUILD_JOBS="1", RAYON_NUM_THREADS="1",
                         CARGO_BUILD_TARGET=TARGET, RUSTFLAGS="-C debuginfo=2",
                         CARGO_TARGET_DIR=str(formal.CACHE / "shieldd-ka-binary-target"))
        bound = {"experiment": Path(__file__), "harness": HARNESS, "matrix": MATRIX,
                 "qualification_validator": formal.ROOT / "decaf_go_binary.py",
                 "source_exporter": formal.ROOT / "decaf_fiat_build.py"}
        hashes = {name: formal.file_digest(path) for name, path in bound.items()}
        pilot.report.update(scope="actual key_agreement_with API; one initialized Linux x86-64 snapshot and public generator peer",
                            source_identities={k: matrix["sources"][k] for k in ("shieldd", "rust")}, input_hashes=hashes,
                            negative_control=args.address_control,
                            open_obligations=["arbitrary permitted public peers and runtime entry states",
                                "production executable/build closure", "ARM64", "native functional refinement",
                                "protocol security", "consumer-specific negative controls"],
                            qualification_complete=False)
        if args.address_control:
            pilot.report["scope"] += "; deliberately injected address-leak control"

        def run(case):
            if platform.system() != "Linux" or platform.machine() != "x86_64":
                raise decaf.Blocked("native Linux x86-64 snapshot host required")
            qualification = json.loads((formal.WORK / "decaf-flow-qualification/report.json").read_text())
            validate_qualification(qualification)
            case["qualification"] = qualification
            case["compiler_artifacts"] = {}
            executables = {}
            for name in ("rustc", "cargo"):
                path = Path(pilot.command(["rustup", "which", "--toolchain", RUST, name],
                                         formal.ROOT, case).strip()).resolve(strict=True)
                case["compiler_artifacts"][str(path)] = formal.file_digest(path)
                executables[name] = path
            pilot.env["RUSTC"] = str(executables["rustc"])
            case["compiler_version"] = pilot.command([executables["rustc"], "-vV"], formal.ROOT, case)
            if f"release: {RUST}\n" not in case["compiler_version"]:
                raise decaf.Blocked("unexpected resolved Rust compiler version")
            sysroot = Path(pilot.command([executables["rustc"], "--print", "sysroot"], formal.ROOT, case).strip())
            drivers = list((sysroot / "lib").glob("librustc_driver*.so"))
            if not drivers:
                raise decaf.Blocked("Rust compiler driver inventory missing")
            for path in drivers:
                case["compiler_artifacts"][str(path)] = formal.file_digest(path)
            cache, bare = CACHES["shieldd"]
            if bare:
                raise decaf.Blocked("unexpected Shieldd source cache format")
            revision = matrix["sources"]["shieldd"]["revision"]
            source = pilot.work / "source"
            source.mkdir()
            case["source_exports"] = []
            export_tree(cache, revision, source, pilot.env, case["source_exports"])
            example = source / "crates/crypto/decaf377-ka/examples/formal_key_agreement.rs"
            if example.exists():
                raise decaf.Blocked("formal example would replace committed source")
            example.parent.mkdir(exist_ok=True)
            shutil.copyfile(HARNESS, example)
            case["source_files"] = tree_state(source)
            case["lock_sha256"] = formal.file_digest(source / "Cargo.lock")
            case["build_environment"] = {name: pilot.env[name] for name in
                ("RUSTUP_TOOLCHAIN", "CARGO_BUILD_JOBS", "RAYON_NUM_THREADS", "CARGO_BUILD_TARGET",
                 "RUSTFLAGS", "CARGO_INCREMENTAL", "RUSTC")}
            metadata = json.loads(pilot.command([executables["cargo"], "metadata", "--locked", "--offline",
                                  "--filter-platform", TARGET, "--format-version", "1"], source, case))
            case["resolved_decaf"] = resolved_decaf(metadata, matrix["sources"]["rust"])
            control_flags = ["--check-cfg", "cfg(decaf_address_control)"]
            if args.address_control:
                control_flags += ["--cfg", "decaf_address_control"]
            pilot.command([executables["cargo"], "rustc", "--locked", "--offline", "--release", "-p", "decaf377-ka",
                           "--example", "formal_key_agreement", "--", "-C", "relocation-model=static",
                           "-C", "link-arg=-no-pie", *control_flags], source, case, timeout=1200)
            binary = Path(pilot.env["CARGO_TARGET_DIR"]) / TARGET / "release/examples/formal_key_agreement"
            pilot.command([binary], source, case, timeout=60)
            case["binary_sha256"] = formal.file_digest(binary)
            if args.address_control:
                symbols = pilot.command(["nm", "-S", "--defined-only", binary], source, case)
                matches = re.findall(r"^([0-9a-f]+)\s+([0-9a-f]+)\s+\w\s+decaf_control_store$", symbols, re.M)
                if len(matches) != 1:
                    raise decaf.Blocked("missing or ambiguous injected-store function")
                start, size = map(lambda value: int(value, 16), matches[0])
                case["injected_store_function"] = {"start": start, "size": size}
            pilot.analyze(binary, case, expected="insecure" if args.address_control else "secure", language="rust")
            if args.address_control and case["status"] == "passed":
                analysis_log = pilot.reports / f"{case['id']}-{len(case['commands'])}.log"
                case["injected_store_leaks"] = address_control_leaks(analysis_log.read_text(), start, size)
            case["scope"] = pilot.report["scope"]
            if case["source_files"] != tree_state(source):
                raise decaf.Blocked("source or dependency lock changed during replay")
            if hashes != {name: formal.file_digest(path) for name, path in bound.items()}:
                raise decaf.Blocked("replay inputs changed during execution")
            for path, digest in case["compiler_artifacts"].items():
                if formal.file_digest(Path(path)) != digest:
                    raise decaf.Blocked("compiler artifact changed during replay")
            validate_qualification(qualification)

        pilot.check("address-control" if args.address_control else "actual-key-agreement",
                    "negative-control" if args.address_control else "compiled-trace", run)
        pilot.report["completed"] = True
        pilot.save()
        return 0 if pilot.report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
