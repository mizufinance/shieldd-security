#!/usr/bin/env python3
"""Extract exact runtime decoder boundaries and check their focused F* proofs."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tomllib

import formal
from security import bounded_run

BOUNDARY = Path("crates/crypto/proof-aggregation/src")
PROOFS = Path("crates/crypto/proof-aggregation/formal/snarkpack")


def prepare(checkout, destination):
    destination.mkdir(parents=True)
    src = destination / "src"
    src.mkdir()
    hashes = {}
    for name in ("aggregate_proof_wrapper", "canonical_encoding"):
        source = checkout / BOUNDARY / f"{name}.rs"
        shutil.copyfile(source, src / source.name)
        hashes[str(BOUNDARY / source.name)] = formal.file_digest(source)
    (src / "lib.rs").write_text("pub mod aggregate_proof_wrapper;\npub mod canonical_encoding;\n")
    (destination / "Cargo.toml").write_text('[package]\nname = "shieldd-sdk-proof-aggregation"\nversion = "0.0.0"\nedition = "2021"\n[workspace]\n')
    return hashes


def check(crate, report_dir, env):
    pins = tomllib.loads((formal.ROOT / PROOFS / "toolchain.toml").read_text())["toolchain"]
    fstar = os.environ.get("FSTAR_BIN") or shutil.which("fstar.exe") or shutil.which("fstar")
    if not fstar:
        raise RuntimeError("pinned F* executable not found")
    versions = {}
    for name, command, pin in [("hax", ["cargo", "hax", "--version"], pins["hax_fstar"].lstrip("v")),
                               ("fstar", [fstar, "--version"], pins["fstar"].lstrip("v")),
                               ("z3", ["z3", "--version"], pins["z3"])]:
        versions[name] = subprocess.check_output(command, env=env, text=True, stderr=subprocess.STDOUT).strip()
        if pin not in versions[name]:
            raise RuntimeError(f"{name} version does not match {pin}")
    (report_dir / "tool-versions.json").write_text(json.dumps(versions, indent=2) + "\n")
    bounded_run(["cargo", "hax", "into", "-i", "-** +shieldd_sdk_proof_aggregation::aggregate_proof_wrapper::encode_wrapped_aggregate_proof +shieldd_sdk_proof_aggregation::aggregate_proof_wrapper::decode_wrapped_aggregate_proof +shieldd_sdk_proof_aggregation::aggregate_proof_wrapper::decode_wrapped_aggregate_proof_inner_range +shieldd_sdk_proof_aggregation::canonical_encoding::canonical_encoding_matches", "fstar"], crate, env, report_dir / "extraction.log",
                crate / "unused-corpus", report_dir, 900)
    libs = Path(os.environ.get("HAX_PROOF_LIBS_HOME", str(Path.home() / f'.local/opt/hax-{pins["hax_fstar"].lstrip("v")}/hax-lib/proof-libs/fstar')))
    support = crate / "support"
    support.mkdir()
    for name in ("core", "rust_primitives"):
        shutil.copytree(libs / name, support / name)
    shutil.copytree(libs.parent.parent / "proofs/fstar/extraction", support / "hax-lib")
    for path in support.rglob("*"):
        if path.suffix in (".fst", ".fsti"):
            text = path.read_text()
            for pattern, replacement in [(r"pred:\s*Type0", "pred: Prims.prop"), (r"->\s*Type0([;)\n])", r"-> Prims.prop\1"), (r"\((p|v__formula): Type0\)", r"(\1: Prims.prop)")]:
                text = re.sub(pattern, replacement, text)
            path.write_text(text)
    formal.run(["python3", str(formal.ROOT / "scripts/prepare_snarkpack_fstar_support.py"), str(support)], cwd=formal.ROOT, env=env)
    (support / "FStar.Mul.fst").write_text("module FStar.Mul\n")
    flags = ["--cache_off"]
    for directory in (support, support / "core", support / "rust_primitives", support / "hax-lib", crate / "proofs/fstar/extraction", formal.ROOT / PROOFS / "fstar", formal.ROOT / "decoder"):
        flags += ["--include", str(directory)]
    for proof in (formal.ROOT / PROOFS / "fstar/WrapperProofs.fst", formal.ROOT / "decoder/CanonicalEncodingProofs.fst", formal.ROOT / "decoder/WrapperBoundaryProofs.fst"):
        bounded_run([fstar, *flags, str(proof)], crate, env, report_dir / f"{proof.stem}.log",
                    crate / "unused-corpus", report_dir, 900)
    shutil.copytree(crate / "proofs/fstar/extraction", report_dir / "extraction")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    formal.add_source_arguments(parser)
    args = parser.parse_args()
    with formal.exclusive_lock():
        reports = formal.WORK / "decoder-contract-report"
        if reports.exists():
            shutil.rmtree(reports)
        reports.mkdir(parents=True)
        checkout = formal.WORK / "decoder-contract-source"
        crate = formal.WORK / "decoder-contract"
        if crate.exists():
            shutil.rmtree(crate)
        mirror = None
        report = {"candidate_revision": None, "status": "running", "full_certification": False,
                  "scope": ["wrapper parsing and exact inner-byte exposure", "canonical byte equality"],
                  "excluded": ["Arkworks deserialization", "curve/subgroup validity", "allocator behavior", "circuit soundness"]}
        env = dict(os.environ, GIT_LFS_SKIP_SMUDGE="1", CARGO_BUILD_JOBS="2", RAYON_NUM_THREADS="2", LEAN_NUM_THREADS="1")
        try:
            source, ref, sha = formal.resolve_inputs(args)
            report["candidate_revision"] = sha
            report["security_revision"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=formal.ROOT, text=True).strip()
            report["proof_hashes"] = {str(path.relative_to(formal.ROOT)): formal.file_digest(path) for path in [formal.ROOT / PROOFS / "fstar/WrapperProofs.fst", *sorted((formal.ROOT / "decoder").glob("*.fst"))]}
            mirror = formal.prepare_mirror(source, ref)
            formal.remove_registered_worktree(mirror, checkout)
            formal.run(["git", "--git-dir", str(mirror), "worktree", "add", "--detach", str(checkout), sha], cwd=formal.ROOT, env=env)
            report["source_hashes"] = prepare(checkout, crate)
            check(crate, reports, env)
            report["status"] = "passed"
        except Exception as error:
            report["status"] = "failed"
            report["error"] = str(error)
            raise
        finally:
            (reports / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
            if mirror is not None:
                formal.remove_registered_worktree(mirror, checkout)


if __name__ == "__main__":
    main()
