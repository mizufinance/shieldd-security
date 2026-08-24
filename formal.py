#!/usr/bin/env python3
"""Compose a pinned Shieldd checkout and run formal work transactionally."""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Iterator, Sequence


ROOT = Path(__file__).resolve().parent
WORK = ROOT / ".work"
CACHE = ROOT / ".cache"
LOCK_PATH = ROOT / "shieldd.lock"
OWNERSHIP_PATH = ROOT / "formal-files.json"


class FormalError(RuntimeError):
    pass


def read_json(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict):
        raise FormalError(f"{path} must contain a JSON object")
    return value


def run(
    args: Sequence[str],
    *,
    cwd: Path,
    env: dict[str, str] | None = None,
    capture: bool = False,
) -> str:
    result = subprocess.run(
        list(args),
        cwd=cwd,
        env=env,
        check=False,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.PIPE if capture else None,
    )
    if result.returncode != 0:
        detail = ""
        if capture:
            detail = f"\n{result.stdout}{result.stderr}".rstrip()
        raise FormalError(f"command failed ({result.returncode}): {' '.join(args)}{detail}")
    return (result.stdout or "").strip()


def exact_commit(source: str, requested: str) -> str:
    value = run(
        ["git", "rev-parse", "--verify", f"{requested}^{{commit}}"],
        cwd=Path(source),
        capture=True,
    ) if Path(source).exists() else requested
    if len(value) != 40 or any(ch not in "0123456789abcdef" for ch in value.lower()):
        raise FormalError(f"Shieldd ref did not resolve to a full commit SHA: {value}")
    return value.lower()


@contextlib.contextmanager
def exclusive_lock() -> Iterator[None]:
    WORK.mkdir(parents=True, exist_ok=True)
    path = WORK / "formal.lock"
    descriptor: int | None = None
    for attempt in range(2):
        try:
            descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            break
        except FileExistsError as error:
            try:
                text = path.read_text(encoding="utf-8").strip()
                owner = int(text.removeprefix("pid="))
                os.kill(owner, 0)
            except (OSError, ValueError):
                if attempt == 0:
                    path.unlink(missing_ok=True)
                    continue
            raise FormalError(f"another formal command owns {path}") from error
    if descriptor is None:
        raise FormalError(f"could not acquire {path}")
    try:
        os.write(descriptor, f"pid={os.getpid()}\n".encode())
        os.close(descriptor)
        yield
    finally:
        path.unlink(missing_ok=True)


def ignored(_directory: str, names: list[str]) -> set[str]:
    ignored_names = {".lake", ".generated", "__pycache__"}
    return {name for name in names if name in ignored_names or name.endswith(".pyc")}


def copy_path(source: Path, destination: Path) -> None:
    if source.is_dir():
        shutil.copytree(
            source,
            destination,
            dirs_exist_ok=True,
            ignore=ignored,
            copy_function=shutil.copy2,
        )
    elif source.is_file():
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
    else:
        raise FormalError(f"owned path is missing: {source.relative_to(ROOT)}")


def _ignored_path(path: Path) -> bool:
    return any(
        part in {".lake", ".generated", "__pycache__"} or part.endswith(".pyc")
        for part in path.parts
    )


def sync_path(source: Path, destination: Path) -> None:
    """Incrementally mirror an owned path without physical file aliases."""
    if source.is_file():
        destination.parent.mkdir(parents=True, exist_ok=True)
        source_stat = source.stat()
        destination_stat = destination.stat() if destination.is_file() else None
        if destination_stat is None or (
            source_stat.st_size != destination_stat.st_size
            or source_stat.st_mtime_ns != destination_stat.st_mtime_ns
        ):
            shutil.copy2(source, destination)
        return
    if not source.is_dir():
        raise FormalError(f"owned path is missing: {source.relative_to(ROOT)}")
    destination.mkdir(parents=True, exist_ok=True)
    source_files = {
        path.relative_to(source)
        for path in source.rglob("*")
        if path.is_file() and not _ignored_path(path.relative_to(source))
    }
    destination_files = {
        path.relative_to(destination)
        for path in destination.rglob("*")
        if path.is_file() and not _ignored_path(path.relative_to(destination))
    }
    for relative in sorted(destination_files - source_files, reverse=True):
        (destination / relative).unlink()
    for relative in sorted(source_files):
        sync_path(source / relative, destination / relative)


def merge_path(source: Path, destination: Path, checkout: Path, relative: str, sha: str) -> None:
    """Overlay a shared directory while preserving files owned by Shieldd."""

    if not source.is_dir():
        raise FormalError(f"merged path is not a directory: {source.relative_to(ROOT)}")
    run(["git", "restore", "--source", sha, "--worktree", "--", relative], cwd=checkout)
    tracked_output = run(
        ["git", "ls-tree", "-r", "--name-only", sha, "--", relative],
        cwd=checkout,
        capture=True,
    )
    tracked = {line.strip() for line in tracked_output.splitlines() if line.strip()}
    source_files = {
        path.relative_to(source)
        for path in source.rglob("*")
        if path.is_file() and not _ignored_path(path.relative_to(source))
    }
    if destination.exists():
        destination_files = {
            path.relative_to(destination)
            for path in destination.rglob("*")
            if path.is_file() and not _ignored_path(path.relative_to(destination))
        }
        for child in sorted(destination_files - source_files, reverse=True):
            checkout_relative = (Path(relative) / child).as_posix()
            if checkout_relative not in tracked:
                (destination / child).unlink()
    for child in sorted(source_files):
        sync_path(source / child, destination / child)


def parse_lfs_pointer(text: str, relative: str) -> tuple[str, int]:
    match = re.fullmatch(
        r"version https://git-lfs\.github\.com/spec/v1\n"
        r"oid sha256:([0-9a-f]{64})\n"
        r"size ([0-9]+)\n?",
        text,
    )
    if match is None:
        raise FormalError(f"locked Shieldd path is not a canonical LFS pointer: {relative}")
    return match.group(1), int(match.group(2))


def verify_lfs_content(path: Path, relative: str, oid: str, size: int) -> None:
    if not path.is_file() or path.stat().st_size != size:
        raise FormalError(f"Shieldd LFS input size does not match locked pointer: {relative}")
    if file_digest(path) != oid:
        raise FormalError(f"Shieldd LFS input digest does not match locked pointer: {relative}")


def materialize_lfs(source: str, checkout: Path, sha: str) -> None:
    inputs = read_json(OWNERSHIP_PATH).get("lfs_inputs", [])
    if not isinstance(inputs, list) or not inputs or not all(
        isinstance(path, str) and path for path in inputs
    ):
        raise FormalError("formal-files.json must declare non-empty lfs_inputs")
    expected = {
        relative: parse_lfs_pointer(
            run(["git", "show", f"{sha}:{relative}"], cwd=checkout, capture=True),
            relative,
        )
        for relative in inputs
    }
    local = Path(source)
    if local.exists():
        for relative in inputs:
            source_path = local / relative
            destination = checkout / relative
            oid, size = expected[relative]
            try:
                verify_lfs_content(destination, relative, oid, size)
                continue
            except FormalError:
                pass
            verify_lfs_content(source_path, relative, oid, size)
            destination.unlink(missing_ok=True)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_path, destination)
            verify_lfs_content(destination, relative, oid, size)
        return
    include = ",".join(inputs)
    run(
        ["git", "lfs", "pull", "--include", include, "--exclude", ""],
        cwd=checkout,
    )
    for relative, (oid, size) in expected.items():
        verify_lfs_content(checkout / relative, relative, oid, size)


def prepare_mirror(source: str, ref: str) -> Path:
    CACHE.mkdir(parents=True, exist_ok=True)
    mirror = CACHE / "shieldd.git"
    if not mirror.exists():
        run(["git", "clone", "--mirror", source, str(mirror)], cwd=ROOT)
    else:
        run(["git", "remote", "set-url", "origin", source], cwd=mirror)
        run(["git", "fetch", "--prune", "origin", ref], cwd=mirror)
    return mirror


def remove_registered_worktree(mirror: Path, checkout: Path) -> None:
    if checkout.exists():
        resolved = checkout.resolve()
        work_root = WORK.resolve()
        if work_root not in resolved.parents:
            raise FormalError(f"managed checkout escaped {WORK}")
    try:
        run(
            ["git", "--git-dir", str(mirror), "worktree", "remove", "--force", str(checkout)],
            cwd=ROOT,
        )
    except FormalError:
        run(["git", "--git-dir", str(mirror), "worktree", "prune"], cwd=ROOT)
        if checkout.exists():
            shutil.rmtree(checkout)


def remove_orphan_runs(mirror: Path) -> None:
    runs = (WORK / "runs").resolve()
    if not runs.exists():
        return
    run(["git", "--git-dir", str(mirror), "worktree", "prune"], cwd=ROOT)
    listing = run(
        ["git", "--git-dir", str(mirror), "worktree", "list", "--porcelain"],
        cwd=ROOT,
        capture=True,
    )
    registered = {
        Path(line.removeprefix("worktree ")).resolve()
        for line in listing.splitlines()
        if line.startswith("worktree ")
    }
    for candidate in runs.iterdir():
        resolved = candidate.resolve()
        if runs not in resolved.parents:
            continue
        if resolved in registered:
            remove_registered_worktree(mirror, candidate)
            continue
        if candidate.is_dir():
            shutil.rmtree(candidate)
        else:
            candidate.unlink()


def cached_composed_checkout(source: str, ref: str, sha: str) -> Path:
    """Return a reusable, independently copied checkout for read-only gates."""
    mirror = prepare_mirror(source, ref)
    resolved = run(
        ["git", "rev-parse", "--verify", f"{sha}^{{commit}}"],
        cwd=mirror,
        capture=True,
    ).lower()
    if resolved != sha:
        raise FormalError(f"locked Shieldd SHA mismatch: expected {sha}, resolved {resolved}")
    checkout = (WORK / "composed").resolve()
    marker = WORK / "composed.sha"
    previous = marker.read_text(encoding="utf-8").strip() if marker.exists() else ""
    if previous != sha or not (checkout / ".git").exists():
        if checkout.exists() or previous:
            remove_registered_worktree(mirror, checkout)
        checkout_env = os.environ.copy()
        checkout_env["GIT_LFS_SKIP_SMUDGE"] = "1"
        run(
            ["git", "--git-dir", str(mirror), "worktree", "add", "--detach", str(checkout), sha],
            cwd=ROOT,
            env=checkout_env,
        )
        marker.write_text(f"{sha}\n", encoding="utf-8")
    materialize_lfs(source, checkout, sha)
    ownership = read_json(OWNERSHIP_PATH)
    for relative in ownership["overlay_paths"]:
        sync_path(ROOT / relative, checkout / relative)
    for relative in ownership.get("merge_paths", []):
        merge_path(ROOT / relative, checkout / relative, checkout, relative, sha)
    return checkout


@contextlib.contextmanager
def composed_checkout(
    source: str, ref: str, sha: str, *, writable: bool
) -> Iterator[Path]:
    mirror = prepare_mirror(source, ref)
    resolved = run(
        ["git", "rev-parse", "--verify", f"{sha}^{{commit}}"],
        cwd=mirror,
        capture=True,
    ).lower()
    if resolved != sha:
        raise FormalError(f"locked Shieldd SHA mismatch: expected {sha}, resolved {resolved}")
    remove_orphan_runs(mirror)
    runs = WORK / "runs"
    runs.mkdir(parents=True, exist_ok=True)
    checkout = Path(tempfile.mkdtemp(prefix="shieldd-", dir=runs)).resolve()
    if runs.resolve() not in checkout.parents:
        raise FormalError(f"managed checkout escaped {runs}")
    checkout_env = os.environ.copy()
    checkout_env["GIT_LFS_SKIP_SMUDGE"] = "1"
    registered = False
    try:
        run(
            ["git", "--git-dir", str(mirror), "worktree", "add", "--detach", str(checkout), sha],
            cwd=ROOT,
            env=checkout_env,
        )
        registered = True
        materialize_lfs(source, checkout, sha)
        ownership = read_json(OWNERSHIP_PATH)
        for relative in ownership["overlay_paths"]:
            copy_path(ROOT / relative, checkout / relative)
        for relative in ownership.get("merge_paths", []):
            merge_path(ROOT / relative, checkout / relative, checkout, relative, sha)
        yield checkout
    finally:
        if registered or checkout.exists():
            try:
                run(
                    ["git", "--git-dir", str(mirror), "worktree", "remove", "--force", str(checkout)],
                    cwd=ROOT,
                    env=checkout_env,
                )
            except FormalError:
                run(
                    ["git", "--git-dir", str(mirror), "worktree", "prune"],
                    cwd=ROOT,
                )
                if checkout.exists():
                    shutil.rmtree(checkout)


def command_environment() -> dict[str, str]:
    env = os.environ.copy()
    cache_paths = {
        "CARGO_TARGET_DIR": CACHE / "cargo-target",
        "GOCACHE": CACHE / "go-build",
        "GOMODCACHE": CACHE / "go-mod",
        "LEAN_BUILD_TELEMETRY_DIR": CACHE / "lean-telemetry",
    }
    for name, path in cache_paths.items():
        path.mkdir(parents=True, exist_ok=True)
        env.setdefault(name, str(path.resolve()))
    env["LEAN_NUM_THREADS"] = "1"
    if os.name == "nt":
        env["FV_WINDOWS_PYTHON"] = sys.executable
        for name in cache_paths:
            expose_to_wsl(env, name, path=True)
        expose_to_wsl(env, "FV_WINDOWS_PYTHON", path=True)
        expose_to_wsl(env, "LEAN_NUM_THREADS")
    return env


def expose_to_wsl(env: dict[str, str], name: str, *, path: bool = False) -> None:
    entries = [entry for entry in env.get("WSLENV", "").split(":") if entry]
    entries = [entry for entry in entries if entry.split("/", 1)[0] != name]
    entries.append(f"{name}/p" if path else name)
    env["WSLENV"] = ":".join(entries)


def prepare_windows_coverage_extractor(
    checkout: Path, env: dict[str, str]
) -> None:
    if os.name != "nt":
        return
    run(
        ["cargo", "build", "--release", "-q", "-p", "shieldd-constraint-coverage"],
        cwd=checkout,
        env=env,
    )
    binary = Path(env["CARGO_TARGET_DIR"]) / "release/shieldd-constraint-coverage.exe"
    if not binary.is_file():
        raise FormalError(f"coverage extractor was not built: {binary}")
    env["FV_WINDOWS_CONSTRAINT_COVERAGE_BIN"] = str(binary.resolve())
    expose_to_wsl(env, "FV_WINDOWS_CONSTRAINT_COVERAGE_BIN", path=True)


def file_digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def snapshot(root: Path, owned_paths: Sequence[str]) -> dict[str, str]:
    result: dict[str, str] = {}
    for relative in owned_paths:
        path = root / relative
        candidates = [path] if path.is_file() else sorted(path.rglob("*")) if path.exists() else []
        for candidate in candidates:
            if candidate.is_file() and not any(part in {".lake", ".generated", "__pycache__"} for part in candidate.parts):
                key = candidate.relative_to(root).as_posix()
                result[key] = file_digest(candidate)
    return result


def promote(checkout: Path, before: dict[str, str], after: dict[str, str]) -> int:
    changed = sorted(key for key, digest in after.items() if before.get(key) != digest)
    deleted = sorted(set(before) - set(after))
    if not changed and not deleted:
        return 0
    promotion = Path(tempfile.mkdtemp(prefix="promotion-", dir=WORK)).resolve()
    backup = promotion / "backup"
    staged = promotion / "staged"
    applied: list[str] = []
    try:
        for key in changed:
            source = checkout / key
            destination = staged / key
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        for key in changed + deleted:
            destination = ROOT / key
            if destination.exists():
                saved = backup / key
                saved.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(destination, saved)
        try:
            for key in changed:
                destination = ROOT / key
                destination.parent.mkdir(parents=True, exist_ok=True)
                os.replace(staged / key, destination)
                applied.append(key)
            for key in deleted:
                destination = ROOT / key
                destination.unlink(missing_ok=True)
                applied.append(key)
        except Exception:
            for key in reversed(applied):
                saved = backup / key
                destination = ROOT / key
                if saved.exists():
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    os.replace(saved, destination)
                else:
                    destination.unlink(missing_ok=True)
            raise
    finally:
        shutil.rmtree(promotion, ignore_errors=True)
    return len(changed) + len(deleted)


def resolve_inputs(args: argparse.Namespace) -> tuple[str, str, str]:
    lock = read_json(LOCK_PATH)
    source = args.shieldd_source or lock["repository"]
    requested = args.shieldd_ref or lock["sha"]
    sha = exact_commit(source, requested)
    ref = args.shieldd_ref or lock.get("ref") or sha
    if args.shieldd_ref is None and sha != lock["sha"]:
        raise FormalError("shieldd.lock SHA did not resolve exactly")
    return source, ref, sha


def run_gate(args: argparse.Namespace) -> None:
    source, ref, sha = resolve_inputs(args)
    with exclusive_lock():
        checkout = cached_composed_checkout(source, ref, sha)
        env = command_environment()
        if args.gate == "soundness":
            prepare_windows_coverage_extractor(checkout, env)
            if os.name == "nt":
                catalog = run(
                    [
                        sys.executable,
                        str(checkout / "scripts/check-fv-profiles.py"),
                        "--emit-gate-catalog-tsv",
                        "--status",
                        "certified",
                    ],
                    cwd=checkout,
                    capture=True,
                )
                catalog_path = checkout / ".formal-gate-catalog.tsv"
                catalog_path.write_text(f"{catalog}\n", encoding="utf-8", newline="\n")
                env["FV_GATE_CATALOG_FILE"] = catalog_path.name
                expose_to_wsl(env, "FV_GATE_CATALOG_FILE")
            command = ["bash", "scripts/check-lean-circuit-fv.sh", args.mode, "all"]
        else:
            env["SNARKPACK_FV_MODE"] = "publication" if args.mode == "full" else "lean-cache"
            if os.name == "nt":
                expose_to_wsl(env, "SNARKPACK_FV_MODE")
            command = ["bash", "scripts/snarkpack-fv.sh"]
        run(command, cwd=checkout, env=env)
    print(f"formal gate passed for Shieldd {sha}")


def refresh_evidence(args: argparse.Namespace) -> None:
    source, ref, sha = resolve_inputs(args)
    ownership = read_json(OWNERSHIP_PATH)
    generated = ownership["generated_paths"]
    with exclusive_lock():
        env = command_environment()
        if args.check:
            checkout = cached_composed_checkout(source, ref, sha)
            run(
                ["bash", "scripts/check-lean-circuit-fv.sh", "drift", "all"],
                cwd=checkout,
                env=env,
            )
            print(f"formal evidence is current for Shieldd {sha}")
            return
        with composed_checkout(source, ref, sha, writable=True) as checkout:
            prepare_windows_coverage_extractor(checkout, env)
            before = snapshot(checkout, generated)
            selection = "all"
            run(
                ["bash", "scripts/refresh-formal-evidence.sh", selection],
                cwd=checkout,
                env=env,
            )
            validation_env = env.copy()
            validation_env["FV_SEMANTICS_CURRENT"] = "1"
            if os.name == "nt":
                expose_to_wsl(validation_env, "FV_SEMANTICS_CURRENT")
            run(
                ["bash", "scripts/check-lean-circuit-fv.sh", "drift", selection],
                cwd=checkout,
                env=validation_env,
            )
            after = snapshot(checkout, generated)
            count = promote(checkout, before, after)
    print(f"promoted {count} formal evidence files for Shieldd {sha}")


def add_source_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--shieldd-source", help="local Shieldd clone or Git URL")
    parser.add_argument("--shieldd-ref", help="exact local ref/SHA for coordinated work")


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser(description=__doc__)
    commands = root.add_subparsers(dest="command", required=True)
    gate = commands.add_parser("gate")
    gate.add_argument("gate", choices=("soundness", "snarkpack"))
    gate.add_argument("--mode", default="affected", choices=("fast", "drift", "affected", "typed", "release", "full", "static"))
    add_source_arguments(gate)
    gate.set_defaults(handler=run_gate)

    evidence = commands.add_parser("evidence")
    evidence_commands = evidence.add_subparsers(dest="evidence_command", required=True)
    refresh = evidence_commands.add_parser("refresh")
    refresh.add_argument("--all", action="store_true", required=True)
    refresh.add_argument("--check", action="store_true")
    add_source_arguments(refresh)
    refresh.set_defaults(handler=refresh_evidence)
    return root


def main() -> int:
    args = parser().parse_args()
    try:
        args.handler(args)
    except (FormalError, OSError, KeyError, ValueError) as error:
        print(f"formal: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
