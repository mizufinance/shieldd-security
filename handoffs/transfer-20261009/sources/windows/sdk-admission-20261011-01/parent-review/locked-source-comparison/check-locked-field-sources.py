"""Verify cached official archives and extracted sources against the runtime lock."""
import hashlib
import json
import tarfile
import tomllib
from pathlib import Path, PurePosixPath

ROOT = Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
lock_path = ROOT/'runtime-snapshot/Cargo.lock'
lock = tomllib.loads(lock_path.read_text())
registry = Path('/Users/antoinecyr/.cargo/registry')
index = 'index.crates.io-1949cf8c6b5b557f'
wanted = [('bls12_381','0.8.0'), ('ff','0.13.0'), ('group','0.13.0'), ('subtle','2.6.1')]
results = []
for name,version in wanted:
    entries = [p for p in lock['package'] if p['name']==name and p['version']==version]
    assert len(entries)==1 and entries[0]['source']=='registry+https://github.com/rust-lang/crates.io-index'
    package = f'{name}-{version}'
    archive = registry/'cache'/index/(package+'.crate')
    source = registry/'src'/index/package
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    assert digest==entries[0]['checksum']
    records = []
    with tarfile.open(archive,'r:gz') as tar:
        members = tar.getmembers()
        assert len(members)<1000
        seen = set()
        for entry in members:
            if entry.isdir():
                continue
            relative = PurePosixPath(entry.name)
            assert entry.isfile() and not relative.is_absolute() and '..' not in relative.parts
            assert relative.parts[0]==package and entry.size<8*1024*1024
            key = str(relative)
            assert key not in seen
            seen.add(key)
            raw = tar.extractfile(entry).read()
            extracted = source.joinpath(*relative.parts[1:])
            assert not extracted.is_symlink() and extracted.read_bytes()==raw
            records.append({'path':str(PurePosixPath(*relative.parts[1:])), 'bytes':len(raw),
                            'sha256':hashlib.sha256(raw).hexdigest()})
    results.append({'name':name,'version':version,'archive':str(archive),'checksum':digest,
                    'source':str(source),'files':records,'files_checked':len(records)})
report = {'kind':'bounded official cached archive/extracted source identity verification',
          'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
          'cargo_lock_sha256':hashlib.sha256(lock_path.read_bytes()).hexdigest(),
          'packages':results,'kernel_replay':False,'native_correspondence':'OPEN','full_transfer':'OPEN'}
target = Path(__file__).parent/'locked-field-source-identities01.json'
target.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'report':str(target),'packages':len(results),'files':sum(x['files_checked'] for x in results)}))
