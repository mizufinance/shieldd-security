"""Compile the immutable pre-observation Transfer in an isolated exact Git export."""
import hashlib
import json
import os
import signal
from pathlib import Path
import sys
import tarfile
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from security import ROOT, CheckError, run

BASE = '713c2a3e5d7c6332fb4688d90873f099d81bc2c4'


def main():
    if os.name == 'nt':
        raise CheckError('baseline execution requires the whole CLI inside Linux/WSL')
    def deadline(*_):
        # run() handles KeyboardInterrupt by reaping its owned compiler group.
        raise KeyboardInterrupt('baseline total deadline (900 seconds)')
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(900)
    runtime = ROOT / '.work/shieldd-current'
    if run(['git', 'cat-file', '-e', BASE], cwd=runtime, check=False).returncode:
        raise CheckError(f'baseline commit {BASE} is unavailable; acquire full runtime history with repository read credentials')
    archive = ROOT / '.work/transfer-baseline.tar'
    run(['git', 'archive', '--format=tar', f'--output={archive}', BASE], cwd=runtime)
    baseline = ROOT / '.work' / f'baseline-{BASE}'
    with tarfile.open(archive) as tar:
        members = tar.getmembers()
        if not baseline.exists():
            baseline.mkdir()
            tar.extractall(baseline, filter='data')
        expected = set()
        for member in members:
            path = baseline / member.name
            if member.isfile():
                expected.add(member.name)
                if not path.is_file() or path.is_symlink() or path.read_bytes() != tar.extractfile(member).read():
                    raise CheckError(f'modified immutable baseline file: {member.name}')
            elif member.issym():
                expected.add(member.name)
                if not path.is_symlink() or os.readlink(path) != member.linkname:
                    raise CheckError(f'modified immutable baseline link: {member.name}')
            elif not member.isdir():
                raise CheckError(f'unsupported baseline archive member: {member.name}')
        actual = {str(p.relative_to(baseline)) for p in baseline.rglob('*') if p.is_file() or p.is_symlink()}
        if actual != expected:
            raise CheckError('unexpected files in immutable baseline export')
    harness = ROOT / '.work/baseline-harness'
    (harness / 'src/bin').mkdir(parents=True, exist_ok=True)
    expected_harness = {'Cargo.toml', 'Cargo.lock', 'src/bin/transfer-baseline.rs'}
    if any(p.is_symlink() or (p.is_file() and str(p.relative_to(harness)) not in expected_harness)
           for p in harness.rglob('*')):
        raise CheckError('unexpected source or symlink in isolated baseline harness')
    manifest = (ROOT / 'integration/Cargo.toml').read_text().replace('../.work/shieldd-current', str(baseline))
    for dependency in tomllib.loads(manifest)['dependencies'].values():
        if isinstance(dependency, dict) and 'path' in dependency:
            Path(dependency['path']).resolve().relative_to(baseline.resolve())
    (harness / 'Cargo.toml').write_text(manifest)
    (harness / 'Cargo.lock').write_bytes((ROOT / 'integration/Cargo.lock').read_bytes())
    (harness / 'src/bin/transfer-baseline.rs').write_bytes((ROOT / 'integration/src/bin/transfer-baseline.rs').read_bytes())
    output = run(['env', 'CARGO_BUILD_JOBS=1', 'RAYON_NUM_THREADS=1', 'CARGO_ENCODED_RUSTFLAGS=',
        f'CARGO_TARGET_DIR={os.environ.get("CARGO_TARGET_DIR", ROOT / ".cache/cargo-target")}',
        'cargo', '+1.95.0', 'run', '--locked', '--profile', 'ci',
        '--manifest-path', str(harness / 'Cargo.toml'), '--bin', 'transfer-baseline'], timeout=600)
    result = json.loads(output)
    result.update(runtime_base=BASE, archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
        cargo_lock_sha256=hashlib.sha256((baseline/'Cargo.lock').read_bytes()).hexdigest(),
        integration_lock_sha256=hashlib.sha256((harness/'Cargo.lock').read_bytes()).hexdigest(),
        integration_manifest_sha256=hashlib.sha256((ROOT/'integration/Cargo.toml').read_bytes()).hexdigest(),
        rustc=run(['rustc', '+1.95.0', '--version']),
        build={'profile':'ci','cargo_jobs':1,'rustflags':[], 'cwd':'security repository root','bin':'transfer-baseline',
               'cargo_timeout_seconds':600, 'total_timeout_seconds':900})
    signal.alarm(0)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
