#!/usr/bin/env python3
"""Run scoped Shieldd security checks against one exact runtime commit."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
FAMILIES = {"transfer", "reshape1x8", "reshape8x1", "withdrawal", "seizure", "disclosure1", "disclosure32", "history_generation", "history_chunk10"}

class CheckError(RuntimeError):
    pass

def read_json(path: Path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise CheckError(f"duplicate JSON key: {key}")
            result[key] = value
        return result
    return json.loads(path.read_text(encoding="utf-8-sig"), object_pairs_hook=unique)

def run(command, cwd=ROOT, timeout=60, check=True):
    env = dict(os.environ, GIT_NO_REPLACE_OBJECTS="1")
    # Adapter descendants share the outer verifier's group, so its timeout
    # cannot orphan a nested Cargo/Lean/Java invocation.
    nested = os.environ.get("SHIELDD_SECURITY_PROCESS_GROUP") == "owned"
    env["SHIELDD_SECURITY_PROCESS_GROUP"] = "owned"
    options = {"start_new_session": not nested} if os.name != "nt" else {"creationflags": subprocess.CREATE_NEW_PROCESS_GROUP}
    process = subprocess.Popen(command, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, **options)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except (subprocess.TimeoutExpired, KeyboardInterrupt):
        if os.name == "nt":
            stopped = subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"], capture_output=True, timeout=15)
            if stopped.returncode != 0 and process.poll() is None:
                raise CheckError(f"could not terminate verifier process tree {process.pid}; check permissions before starting another job")
        else:
            os.killpg(os.getpgrp() if nested else process.pid, signal.SIGKILL)
        process.wait(timeout=15)
        process.stdout.close()
        process.stderr.close()
        raise
    if not check:
        return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
    if process.returncode:
        raise CheckError(f"command failed ({process.returncode}): {command}\n{stdout}{stderr}")
    return stdout.strip()

def locked_sha(root=ROOT):
    lock = read_json(root / "shieldd.lock")
    sha = lock.get("sha", "")
    if not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{40}", sha) or lock.get("ref") != sha:
        raise CheckError("shieldd.lock must select one full lowercase commit SHA")
    if lock.get("repository") != "https://github.com/mizufinance/shieldd.git":
        raise CheckError("unexpected runtime repository")
    return sha

def runtime_identity(source, sha):
    source = Path(source).resolve()
    if run(["git", "rev-parse", "HEAD"], source) != sha:
        raise CheckError("runtime HEAD differs from shieldd.lock")
    if run(["git", "status", "--porcelain", "--untracked-files=all"], source):
        raise CheckError("runtime checkout is dirty; commit or restore runtime changes first")
    return {"sha": sha, "cargo_lock_sha256": hashlib.sha256((source / "Cargo.lock").read_bytes()).hexdigest(),
            "commonware_provenance_sha256": hashlib.sha256((source / "third_party/commonware-patches/provenance.json").read_bytes()).hexdigest()}

def source_identity(root=ROOT):
    # Git's tracked/nonignored file list includes untracked proof sources but excludes caches.
    paths = run(["git", "ls-files", "--cached", "--others", "--exclude-standard"], root).splitlines()
    digest = hashlib.sha256()
    for relative in sorted(set(paths)):
        path = root / relative
        if path.is_file():
            digest.update(relative.encode() + b"\0" + path.read_bytes() + b"\0")
    return {"revision": run(["git", "rev-parse", "HEAD"], root), "sha256": digest.hexdigest(),
            "dirty": bool(run(["git", "status", "--porcelain", "--untracked-files=all"], root))}

def check_register(root=ROOT):
    locked_sha(root)
    register = read_json(root / "assurance.json")
    if set(register.get("families", {})) != FAMILIES:
        raise CheckError("assurance register must enumerate all nine current families")
    if any(value != "blocked" for value in register["families"].values()):
        raise CheckError("whole-family proofs remain blocked in the pilot")
    if register.get("full_system_certification") != "not_established":
        raise CheckError("pilot evidence cannot establish full-system certification")
    claims = register.get("claims")
    if not isinstance(claims, dict) or set(claims) != {"system", "range_volume", "backend", "snapshot_freeze"}:
        raise CheckError("required assurance claims are missing or unknown")
    for name, claim in claims.items():
        if not isinstance(claim, dict):
            raise CheckError(f"claim must be an object: {name}")
        if claim.get("status") not in {"blocked", "proved", "model_checked", "tested", "assumed", "reviewed"}:
            raise CheckError(f"invalid claim status: {name}")
        if not claim.get("scope") or not claim.get("limits"):
            raise CheckError(f"claim lacks scope or limits: {name}")
    return register

def write_result(path, result):
    """Promote a complete result atomically; failed generation never overwrites it."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as handle:
        temporary = Path(handle.name)
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write("\n")
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)

def execute_pilot(pilot, source, model_only=False):
    if model_only and pilot != 'state':
        raise CheckError('--model-only applies only to the state command')
    if source.resolve() != (ROOT / ".work/shieldd-current").resolve():
        raise CheckError("pilots require .work/shieldd-current: Cargo dependencies must use the checked runtime")
    runtime = runtime_identity(source, locked_sha())
    security = source_identity()
    adapter = ROOT / pilot / "check.py"
    if not adapter.is_file():
        raise CheckError(f"{pilot} pilot has no executed implementation yet")
    command = [sys.executable, str(adapter), "--source", str(source.resolve())]
    if model_only:
        command.append('--model-only')
    timeout_seconds = 4800 if pilot == 'circuits' else 1800
    payload = json.loads(run(command, timeout=timeout_seconds))
    if payload.get("outcome") != "passed":
        raise CheckError(f"{pilot} did not pass")
    if pilot == 'state' and not model_only and payload.get('runtime') is None:
        raise CheckError('full state replay requires actual runtime evidence')
    if runtime_identity(source, locked_sha()) != runtime or source_identity() != security:
        raise CheckError("verification inputs changed during execution; result discarded")
    return {"pilot": 'state-model' if model_only else pilot, "runtime": runtime, "security": security,
            "command": command, "timeout_seconds": timeout_seconds, "evidence": payload}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check", "circuits", "state", "release"])
    parser.add_argument("--source", type=Path, default=ROOT / ".work/shieldd-current")
    parser.add_argument('--model-only', action='store_true', help='state finite model only; does not replace runtime replay')
    args = parser.parse_args()
    try:
        if args.model_only and args.command != 'state':
            raise CheckError('--model-only applies only to the state command')
        register = check_register()
        if args.command == "check":
            print("Current-suite policy valid. Full-system certification: NOT ESTABLISHED.")
            return 0
        if args.command == "release":
            raise CheckError("release blocked: pilot work does not close the nine circuit families and system obligations")
        result = execute_pilot(args.command, args.source, args.model_only)
        write_result(ROOT / ".work/results" / f"{result['pilot']}.json", result)
        print(json.dumps(result, indent=2))
        return 0
    except (CheckError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"security: {error}", file=sys.stderr)
        return 1

if __name__ == "__main__":
    raise SystemExit(main())
