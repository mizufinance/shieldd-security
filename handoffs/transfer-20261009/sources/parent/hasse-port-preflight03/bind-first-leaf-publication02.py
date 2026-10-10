"""Bind immutable producer names to published paths; source-only, no compiler."""
import sys
if not __debug__:
    raise RuntimeError('Optimized Python is unsupported')
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
import hashlib
import json
import os
import tempfile
from pathlib import Path

base = Path(__file__).resolve().parent
digest = lambda raw: hashlib.sha256(raw).hexdigest()
producer = base / 'first-leaf-manifest01.json'
raw = producer.read_bytes()
manifest = json.loads(raw)
mapping = {
    'LICENSE': 'prepared/LICENSE',
    'scope01.json': 'first-leaf-scope01.json',
    'HasseWeil/Foundation/Auxiliary/EllipticDivisibilitySequence.lean':
        'prepared/HasseWeil/Foundation/Auxiliary/EllipticDivisibilitySequence.lean',
}
assert set(mapping) == set(manifest['files'])
assert len(set(mapping.values())) == len(mapping)
entries = {}
before = {producer: raw, Path(__file__).resolve(): Path(__file__).read_bytes()}
for original, published in mapping.items():
    path = base / published
    assert path.resolve().is_relative_to(base.resolve())
    content = path.read_bytes()
    expected = manifest['files'][original]
    assert digest(content) == expected['sha256'] and len(content) == expected['bytes']
    before[path] = content
    entries[original] = {'published_path': published, **expected}
result = {
    'kind': 'immutable-producer-to-publication-path-binding',
    'producer_manifest': {'path': producer.name, 'sha256': digest(raw), 'bytes': len(raw)},
    'files': entries,
    'generator': {'path': Path(__file__).name, 'sha256': digest(before[Path(__file__).resolve()])},
    'inputs_unchanged_during_run': True,
    'kernel_runs': 0,
    'kernel_credit': 0,
    'admission': 'No build admission; source transport metadata only',
    'full_transfer': 'OPEN',
}
output = base / 'first-leaf-publication02.json'
assert not output.exists()
content = (json.dumps(result, indent=2) + '\n').encode()
temporary = None
try:
    with tempfile.NamedTemporaryFile(dir=base, prefix='.first-leaf-publication02-',
                                     suffix='.tmp', delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(content)
    for path, old in before.items():
        assert path.read_bytes() == old, str(path)
    os.replace(temporary, output)
finally:
    if temporary is not None and temporary.exists():
        temporary.unlink()
print(json.dumps({'status': 'passed_source_only', 'files': len(entries),
                  'output_sha256': digest(content), 'kernel_runs': 0}))
