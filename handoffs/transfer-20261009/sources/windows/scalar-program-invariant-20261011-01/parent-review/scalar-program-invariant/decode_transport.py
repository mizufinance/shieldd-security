"""Verify numbered tar.xz transport and extract only bounded plain files."""
import argparse
import base64
import hashlib
import io
import json
import tarfile
import shutil
from pathlib import Path, PurePosixPath

p = argparse.ArgumentParser()
p.add_argument('input', type=Path)
a = p.parse_args()
assert a.input.stat().st_size <= 2 * 1024 * 1024
assert shutil.disk_usage(a.input.parent).free >= 2 * 1024 * 1024 * 1024
chunks = json.loads(a.input.read_bytes())
count = chunks[0]['part_count']
digest = chunks[0]['archive_sha256']
assert len(chunks) == count and count <= 128
assert sorted(c['part'] for c in chunks) == list(range(1, count + 1))
for c in chunks:
    assert c['part_count'] == count and c['archive_sha256'] == digest
    assert hashlib.sha256(c['base64'].encode()).hexdigest() == c['chunk_sha256']
archive = base64.b64decode(''.join(c['base64'] for c in sorted(chunks, key=lambda c: c['part'])), validate=True)
assert len(archive) == 383364 and digest == '9c3be4a7fd1e7e2af8aa06c7836a8dbb10d7dbcd2a1ccf77fa956c484c42b42b'
assert hashlib.sha256(archive).hexdigest() == digest
out = a.input.parent / 'packet01'
out.mkdir(exist_ok=False)
files = []
with tarfile.open(fileobj=io.BytesIO(archive), mode='r:xz') as t:
    members = t.getmembers()
    assert len(members) < 512 and sum(m.size for m in members) < 128 * 1024 * 1024
    for m in members:
        path = PurePosixPath(m.name)
        assert not path.is_absolute() and '..' not in path.parts and '\\' not in m.name and ':' not in m.name
        if m.isdir():
            continue
        assert m.isfile() and not m.issym() and not m.islnk()
        assert not m.name.endswith(('.olean', '.olean.private', '.olean.server', '.ir', '.ilean', '.stdout', '.stderr'))
        data = t.extractfile(m).read()
        assert len(data) == m.size
        target = out / m.name
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as f:
            f.write(data)
        files.append({'name': m.name, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
with (a.input.parent / 'transport01.tar.xz').open('xb') as f:
    f.write(archive)
report = {'archive_sha256': digest, 'archive_bytes': len(archive), 'chunks': count,
          'files': files, 'kind': 'transport only; no kernel replay'}
with (a.input.parent / 'transport-verification01.json').open('x') as f:
    json.dump(report, f, indent=2)
    f.write('\n')
print(json.dumps({'archive_sha256': digest, 'archive_bytes': len(archive), 'files': len(files)}))
