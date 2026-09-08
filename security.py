#!/usr/bin/env python3
"""Run bounded native decoder fuzzing against the exact Shieldd candidate."""
import argparse
import json
import os
import shutil
import signal
import subprocess
import time

import formal

NIGHTLY = "nightly-2025-09-30"
TARGET = "deserialize_aggregate_proof"
FUZZ_DIR = "crates/crypto/proof-aggregation-fuzz"
BYTE_LIMIT = 100 * 1024 * 1024


def inventory(directory):
    return {str(path.relative_to(directory)): {"bytes": path.stat().st_size, "sha256": formal.file_digest(path)}
            for path in sorted(directory.rglob("*")) if path.is_file()}


def size(directory):
    return sum(path.stat().st_size for path in directory.rglob("*") if path.is_file())


def bounded_run(command, cwd, env, log, corpus, reports, timeout):
    started = time.monotonic()
    with log.open("w") as output:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while process.poll() is None:
                if size(corpus) + size(reports) > BYTE_LIMIT:
                    raise RuntimeError("fuzz corpus and reports exceeded 100 MiB")
                if time.monotonic() - started > timeout:
                    raise RuntimeError("verification process exceeded its wall-clock budget")
                time.sleep(1)
        finally:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                pass
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
    if process.returncode:
        raise RuntimeError(f"verification process failed ({process.returncode}); see {log}")
    if size(corpus) + size(reports) > BYTE_LIMIT:
        raise RuntimeError("fuzz outputs exceeded 100 MiB")


def fuzz(args):
    with formal.exclusive_lock():
        fuzz_locked(args)


def fuzz_locked(args):
    reports = formal.WORK / "fuzz-report"
    corpus = formal.CACHE / "decoder-corpus"
    if reports.exists():
        shutil.rmtree(reports)
    reports.mkdir(parents=True)
    corpus.mkdir(parents=True, exist_ok=True)
    findings = reports / "findings"
    findings.mkdir()
    report = {
        "candidate_revision": None,
        "target": TARGET, "toolchain": NIGHTLY, "status": "running",
        "limits": {"seconds": args.seconds, "workers": 1, "input_bytes": 131073,
                   "rss_mib": 2048, "input_seconds": 15, "output_bytes": BYTE_LIMIT},
        "full_certification": False,
    }
    checkout = formal.WORK / "fuzz-source"
    mirror = None
    env = dict(os.environ, GIT_LFS_SKIP_SMUDGE="1", CARGO_BUILD_JOBS="2",
               RAYON_NUM_THREADS="2", GOMAXPROCS="2",
               CARGO_TARGET_DIR=str(formal.CACHE / "fuzz-target"))
    try:
        source, ref, sha = formal.resolve_inputs(args)
        report["candidate_revision"] = sha
        report["security_revision"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=formal.ROOT, text=True).strip()
        report["cargo_fuzz_version"] = subprocess.check_output(["cargo", f"+{NIGHTLY}", "fuzz", "--version"], text=True).strip()
        report["rustc_version"] = subprocess.check_output(["rustc", f"+{NIGHTLY}", "--version"], text=True).strip()
        mirror = formal.prepare_mirror(source, ref)
        formal.remove_registered_worktree(mirror, checkout)
        formal.run(["git", "--git-dir", str(mirror), "worktree", "add", "--detach", str(checkout), sha], cwd=formal.ROOT, env=env)
        report["cargo_lock_sha256"] = formal.file_digest(checkout / "Cargo.lock")
        seeds = checkout / FUZZ_DIR / "corpus" / TARGET
        report["curated_seeds"] = inventory(seeds)
        for path in seeds.iterdir():
            if path.is_file():
                shutil.copyfile(path, corpus / path.name)
        if size(corpus) > BYTE_LIMIT:
            raise RuntimeError("cached corpus exceeds 100 MiB")
        command = ["cargo", f"+{NIGHTLY}", "fuzz", "run", "--fuzz-dir", FUZZ_DIR, "--sanitizer", "address", TARGET]
        limits = ["-max_len=131073", "-rss_limit_mb=2048", "-timeout=15",
                  f"-artifact_prefix={findings}/"]
        # Explicit files replay every curated case, including oversized boundaries.
        bounded_run(command + [str(path) for path in sorted(seeds.iterdir()) if path.is_file()] + ["--", *limits],
                    checkout, env, reports / "replay.log", corpus, reports, 1800)
        bounded_run(command + [str(corpus), "--", *limits, f"-max_total_time={args.seconds}"],
                    checkout, env, reports / "campaign.log", corpus, reports, args.seconds + 180)
        report["status"] = "passed"
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        report["corpus"] = inventory(corpus)
        report["findings"] = inventory(findings)
        (reports / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        if mirror is not None:
            formal.remove_registered_worktree(mirror, checkout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["fuzz"])
    parser.add_argument("--seconds", type=int, default=60)
    formal.add_source_arguments(parser)
    args = parser.parse_args()
    if not 1 <= args.seconds <= 1800:
        parser.error("campaign duration must be between 1 and 1800 seconds")
    fuzz(args)


if __name__ == "__main__":
    main()
