"""Bounded read-only source fetch for the two exact locked SDK dependencies.

No Cargo/build/script execution, dependency-cache mutation or semantic proof
credit. Archives must match the pinned runtime Cargo.lock checksums exactly.
Only regular Rust source files are extracted into this fresh scratch task.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tomllib
import urllib.request

ROOT = Path(__file__).resolve().parent
RUNTIME = Path('C:/src/shieldd-pr160-844389ee')
CAP, SOURCE_CAP = 16 * 1024**2, 2 * 1024**2
def pin(path):
    path = Path(path)
    with path.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
def usage():
    total = sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())
    assert total < CAP
    return total
def git(*args):
    return subprocess.check_output(['git', '-c', 'core.fsmonitor=false', *args], cwd=RUNTIME,
                                   env=dict(os.environ, GIT_OPTIONAL_LOCKS='0'))
assert git('rev-parse', 'HEAD').decode().strip() == '844389ee069e1fb2e576708842d0b389b4d9a44a'
assert not git('status', '--porcelain=v1', '-z', '--untracked-files=all')
assert shutil.disk_usage(ROOT).free > 2 * 1024**3
lock = RUNTIME / 'Cargo.lock'
lock_record = pin(lock)
data = tomllib.loads(lock.read_text())
packages = [p for p in data['package'] if p['name'] in ['jubjub', 'reddsa']]
assert [(p['name'], p['version'], p['checksum']) for p in packages] == [
    ('jubjub', '0.10.0', '8499f7a74008aafbecb2a2e608a3e13e4dd3e84df198b604451efe93f2de6e61'),
    ('reddsa', '0.5.2', '4784b85c8bfd17b36b86e664e6e504ecdb586001086ee23749e4a633bbb84832')]
inputs = ROOT / 'inputs'
inputs.mkdir(exist_ok=False)
shutil.copyfile(lock, inputs / 'Cargo.lock')
assert pin(inputs / 'Cargo.lock')['sha256'] == lock_record['sha256']
records = []
for package in packages:
    identity = package['name'] + '-' + package['version']
    url = 'https://static.crates.io/crates/' + package['name'] + '/' + identity + '.crate'
    archive = inputs / (identity + '.crate')
    with urllib.request.urlopen(url, timeout=20) as response, archive.open('xb') as target:
        size = 0
        while True:
            chunk = response.read(65536)
            if not chunk:
                break
            size += len(chunk)
            assert size <= SOURCE_CAP
            target.write(chunk)
            usage()
    assert pin(archive)['sha256'] == package['checksum']
    extracted = []
    destination_root = ROOT / 'sources' / identity
    with tarfile.open(archive, 'r:gz') as tar:
        members = [m for m in tar.getmembers() if m.name.startswith(identity + '/src/') and m.name.endswith('.rs')]
        assert members and len(members) <= 32 and sum(m.size for m in members) <= SOURCE_CAP
        for member in members:
            assert member.isfile() and 0 <= member.size <= SOURCE_CAP
            relative = Path(member.name.removeprefix(identity + '/'))
            assert not relative.is_absolute() and '..' not in relative.parts
            target = destination_root / relative
            assert destination_root.resolve() in target.resolve().parents
            target.parent.mkdir(parents=True, exist_ok=True)
            assert not target.exists()
            with tar.extractfile(member) as stream, target.open('xb') as output:
                shutil.copyfileobj(stream, output, length=65536)
            assert target.stat().st_size == member.size
            extracted.append(pin(target)); usage()
    records.append({'package': package, 'url': url, 'archive': pin(archive), 'rust_sources': extracted})
assert pin(lock) == lock_record
assert not git('status', '--porcelain=v1', '-z', '--untracked-files=all')
receipt = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a', 'runtime_clean': True,
           'cargo_lock': lock_record, 'recipe': pin(Path(__file__)), 'packages': records,
           'artifact_bytes': usage(), 'kernel_credit': 0, 'runtime_test_credit': 0,
           'semantic_correspondence_credit': 0, 'certification_credit': 0,
           'scope': 'Exact locked dependency source identities for reading generator/admission/group operations. Hash equality establishes archive identity only; no native interpretation or proof claim.'}
(ROOT / 'source-identities.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(json.dumps({'receipt': pin(ROOT / 'source-identities.json'),
                  'packages': [(r['package']['name'], r['package']['version'], len(r['rust_sources'])) for r in records],
                  'artifact_bytes': usage(), 'kernel_credit': 0}))
