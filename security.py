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
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
FAMILIES = {"transfer", "reshape1x8", "reshape8x1", "withdrawal", "seizure", "disclosure1", "disclosure32"}

class CheckError(RuntimeError):
    pass

def read_json_bytes(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise CheckError(f"duplicate JSON key: {key}")
            result[key] = value
        return result
    return json.loads(data.decode('utf-8-sig'), object_pairs_hook=unique)


_OMITTED_EXPECTATION = object()


def verified_bytes(path, expected=_OMITTED_EXPECTATION):
    """One regular-file read for both identity and interpretation; no new authority."""
    path = Path(path)
    before = path.lstat()
    if path.is_symlink() or not stat.S_ISREG(before.st_mode):
        raise CheckError(f'missing or redirected required artifact: {path}')
    fields = ('st_dev', 'st_ino', 'st_mode', 'st_uid', 'st_gid', 'st_nlink',
              'st_size', 'st_mtime_ns', 'st_ctime_ns')
    metadata = lambda value, keys=fields: tuple(getattr(value, key) for key in keys)
    # Windows pathname and opened-handle ctime observations can differ even for
    # the same file. Keep each nine-field observation stable through the read;
    # bridge them by the other eight identity fields rather than normalize ctime.
    shared = fields[:-1] if os.name == 'nt' else fields
    with path.open('rb') as handle:
        opened = os.fstat(handle.fileno())
        if metadata(opened, shared) != metadata(before, shared):
            raise CheckError(f'opened artifact identity changed: {path}')
        data = handle.read()
        if metadata(os.fstat(handle.fileno())) != metadata(opened):
            raise CheckError(f'opened artifact changed during read: {path}')
    digest = hashlib.sha256(data).hexdigest()
    if metadata(path.lstat()) != metadata(before):
        raise CheckError(f'artifact changed during read: {path}')
    if expected is not _OMITTED_EXPECTATION and (not isinstance(expected, str)
            or not re.fullmatch(r'[0-9a-f]{64}', expected) or digest != expected):
        raise CheckError(f'predeclared artifact identity mismatch: {path}')
    return data


def read_json(path: Path):
    return read_json_bytes(verified_bytes(path))

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
        raise CheckError("assurance register must enumerate all seven current families")
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

TRANSFER_SLICE_SHA = '844389ee069e1fb2e576708842d0b389b4d9a44a'
TRANSFER_SLICE_THEOREMS = {
    'projection': ['ShielddSecurity.RuntimeTransferStatement.projection_exact',
                   'ShielddSecurity.RuntimeTransferStatement.projection_injective'],
    'permanent_spend': ['ShielddSecurity.PermanentSpend.' + name for name in
                        ('branch_sound', 'branch_gates_complete', 'assignment_branch_sound',
                         'required_input_real', 'required_assignment_real')],
}

def transfer_slice_proof_inputs(root=ROOT):
    """Versioned digest; only the two derived register pointers are masked."""
    paths = sorted(set(run(['git', 'ls-files', '--cached', '--others', '--exclude-standard'], root).splitlines()))
    if 'assurance.json' not in paths:
        raise CheckError('assurance register must be a proof input')
    digest = hashlib.sha256()
    for relative in paths:
        path = root / relative
        if not path.is_file():
            continue
        data = path.read_bytes()
        if relative == 'assurance.json':
            register = read_json_bytes(data)
            try:
                receipt = register['claims']['system']['development_evidence']['reduced_transfer_slice']['receipt']
                if set(receipt) != {'path', 'sha256'}:
                    raise CheckError('derived receipt object must have exactly path and sha256')
                for key in ('path', 'sha256'):
                    receipt[key] = '__DERIVED_REDUCED_TRANSFER_RECEIPT__'
            except (KeyError, TypeError) as error:
                raise CheckError('substantive reduced slice entry and both derived pointers must preexist') from error
            data = json.dumps(register, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode('utf-8')
        digest.update(relative.encode('utf-8') + b'\0' + data + b'\0')
    return {'version': 'reduced-transfer-proof-inputs-v1', 'sha256': digest.hexdigest()}

def prepare_transfer_slice(source, qualification, candidate_dir):
    """Route the named circuit scope through the existing circuit checker."""
    from circuits import check as checker
    try:
        return checker.prepare_transfer_slice(source, qualification, candidate_dir)
    except checker.CheckError as error:
        raise CheckError(str(error)) from error

def verify_transfer_slice_link(source, observation, expected_receipt_sha256):
    """Validate only linkage to an independently retained publication pin."""
    if (not isinstance(expected_receipt_sha256, str)
            or not re.fullmatch(r'[0-9a-f]{64}', expected_receipt_sha256)):
        raise CheckError('an independently retained expected published receipt SHA is required')
    sha = locked_sha()
    if sha != TRANSFER_SLICE_SHA:
        raise CheckError('transfer-slice linkage supports only the exact PR160 lock')
    path = ROOT / '.work/results/transfer-slice.json'
    receipt_bytes = verified_bytes(path, expected_receipt_sha256)
    result = read_json_bytes(receipt_bytes)
    roles = {'comparison', 'decision', 'projection', 'permanent_spend', 'controls', 'source_joins'}
    if (result.get('pilot') != 'transfer-slice'
            or result.get('outcome') != 'qualified_development_artifacts_unlinked'
            or result.get('full_system_certification') != 'not_established'
            or result.get('register_linkage') != 'requires_separate_post_link_validation'
            or result.get('theorems') != TRANSFER_SLICE_THEOREMS
            or result.get('approach') not in {'clean', 'direct-lean'}
            or set(result.get('artifacts', {})) != roles
            or not result.get('assumptions') or not result.get('limits')
            or result.get('raw_pre') != result.get('raw_post')
            or not isinstance(result.get('raw_pre'), dict)
            or result.get('proof_inputs', {}).get('version') != 'reduced-transfer-proof-inputs-v1'):
        raise CheckError('published receipt has wrong narrow pilot/outcome/interface shape')

    def current_inputs():
        register_bytes = verified_bytes(ROOT / 'assurance.json')
        register = read_json_bytes(register_bytes)
        if check_register() != register:
            raise CheckError('register changed during publication observation')
        state = {'runtime': runtime_identity(source, sha),
                 'proof_inputs': transfer_slice_proof_inputs(),
                 'raw_source_post_link': source_identity(),
                 'raw_register_post_link_sha256': hashlib.sha256(register_bytes).hexdigest()}
        verified_bytes(ROOT / 'assurance.json', state['raw_register_post_link_sha256'])
        return state, register

    before, register = current_inputs()
    try:
        entry = register['claims']['system']['development_evidence']['reduced_transfer_slice']
        link = entry['receipt']
        authority_path = str((ROOT / entry['qualification']['path']).resolve())
        authority_sha256 = entry['qualification']['sha256']
    except (KeyError, TypeError) as error:
        raise CheckError('missing predeclared slice linkage/qualification') from error
    if (register['claims']['system']['status'] != 'blocked'
            or link != {'path': '.work/results/transfer-slice.json', 'sha256': expected_receipt_sha256}
            or result['runtime'] != before['runtime']
            or result['proof_inputs'] != before['proof_inputs']
            or result.get('checked_raw_refs', {}).get(authority_path) != authority_sha256):
        raise CheckError('published pinned receipt linkage/runtime/normalized inputs mismatch')
    after, register_after = current_inputs()
    if after != before or register_after != register or verified_bytes(path, expected_receipt_sha256) != receipt_bytes:
        raise CheckError('whole-phase publication inputs or pinned receipt changed')
    observation = Path(observation).resolve()
    if not observation.is_relative_to((ROOT / '.work').resolve()) or observation.exists():
        raise CheckError('fresh publication observation under .work required')
    data = {'scope': 'post-link publication observation only; not requalification or certification',
            'expected_receipt_sha256': expected_receipt_sha256,
            'receipt_sha256': hashlib.sha256(receipt_bytes).hexdigest(),
            **before, 'whole_phase_inputs_equal': True}
    with observation.open('x', encoding='utf-8') as handle:
        json.dump(data, handle, sort_keys=True); handle.write('\n'); handle.flush(); os.fsync(handle.fileno())
    final, final_register = current_inputs()
    if final != before or final_register != register or verified_bytes(path, expected_receipt_sha256) != receipt_bytes:
        raise CheckError('publication inputs drifted after observation write; retain failed observation')
    return data

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check", "circuits", "state", "release"])
    parser.add_argument("--source", type=Path, default=ROOT / ".work/shieldd-current")
    parser.add_argument('--model-only', action='store_true', help='state finite model only; does not replace runtime replay')
    parser.add_argument('--scope', choices=['legacy', 'transfer-slice'], default='legacy')
    parser.add_argument('--qualified-receipts', type=Path)
    parser.add_argument('--candidate-dir', type=Path)
    parser.add_argument('--verify-link', action='store_true')
    parser.add_argument('--publication-observation', type=Path)
    parser.add_argument('--expected-published-receipt-sha256', help='independently retained publication SHA; link observation only')
    args = parser.parse_args()
    try:
        if args.model_only and args.command != 'state':
            raise CheckError('--model-only applies only to the state command')
        register = check_register()
        if args.scope == 'transfer-slice':
            if args.command != 'circuits' or args.model_only:
                raise CheckError('--scope transfer-slice applies only to circuits')
            if args.verify_link:
                if (not args.publication_observation or not args.expected_published_receipt_sha256
                        or args.qualified_receipts or args.candidate_dir):
                    raise CheckError('post-link validation requires observation and independently retained receipt SHA only')
                result = verify_transfer_slice_link(args.source, args.publication_observation, args.expected_published_receipt_sha256)
            else:
                if (not args.qualified_receipts or not args.candidate_dir or args.publication_observation
                        or args.expected_published_receipt_sha256):
                    raise CheckError('slice requires explicit qualified receipts and a fresh candidate directory')
                result = prepare_transfer_slice(args.source, args.qualified_receipts, args.candidate_dir)
                write_result(ROOT / '.work/results/transfer-slice.json', result)
            print(json.dumps(result, indent=2))
            return 0
        if (args.qualified_receipts or args.candidate_dir or args.verify_link
                or args.publication_observation or args.expected_published_receipt_sha256):
            raise CheckError('slice arguments require --scope transfer-slice')
        if args.command == "check":
            print("Current-suite policy valid. Full-system certification: NOT ESTABLISHED.")
            return 0
        if args.command == "release":
            raise CheckError("release blocked: pilot work does not close the seven circuit families and system obligations")
        result = execute_pilot(args.command, args.source, args.model_only)
        write_result(ROOT / ".work/results" / f"{result['pilot']}.json", result)
        print(json.dumps(result, indent=2))
        return 0
    except (CheckError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"security: {error}", file=sys.stderr)
        return 1

if __name__ == "__main__":
    raise SystemExit(main())
