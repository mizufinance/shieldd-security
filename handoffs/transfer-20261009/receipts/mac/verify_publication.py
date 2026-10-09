"""Verify shipped source/receipt identities; this does not rerun verification."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[2]
manifest = json.loads((root / 'receipts/mac/publication-manifest.json').read_text())
for entry in manifest['files']:
    relative = Path(entry['path'])
    assert not relative.is_absolute() and '..' not in relative.parts
    raw = (root / relative).read_bytes()
    assert len(raw) == entry['bytes'], entry['path']
    assert hashlib.sha256(raw).hexdigest() == entry['sha256'], entry['path']
print(json.dumps({'verified_shipped_files': len(manifest['files']),
                  'runtime_pin': manifest['runtime_pin'], 'full_transfer': 'OPEN'}))
