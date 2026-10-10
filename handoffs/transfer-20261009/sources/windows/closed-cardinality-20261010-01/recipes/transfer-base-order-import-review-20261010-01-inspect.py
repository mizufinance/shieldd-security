"""Read-only review of exact old owned source/object closure; no replay credit."""
import hashlib
import json
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
OLD = DIAG / 'transfer-implementation-20261002/windows-point-order-20261009-01-kernel'
PROJECT = OLD / 'project/ShielddSecurity'
def pin(path):
    with path.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
owned = {}
external = set()
def visit(name):
    if not name.startswith('ShielddSecurity.'):
        external.add(name); return
    if name in owned: return
    stem = name.split('.')[-1]
    source = PROJECT / (stem + '.lean')
    obj = PROJECT / (stem + '.olean')
    assert source.is_file() and obj.is_file(), name
    imports = re.findall(r'^import\s+([A-Za-z0-9_.]+)', source.read_text(), re.M)
    owned[name] = {'source': pin(source), 'object': pin(obj), 'imports': imports}
    for item in imports: visit(item)
visit('ShielddSecurity.ConcretePointOrder01')
floor = json.loads((DIAG / 'transfer-external-floor-complete-20261010-10/external-floor.json').read_text())
print(json.dumps({'floor_keys': list(floor)}))
gaps = sorted(external - set(floor['modules']))
manifest = json.loads((OLD / 'manifest.json').read_text(encoding='utf-8-sig'))
review = {'old_manifest': pin(OLD / 'manifest.json'), 'owned': owned,
    'direct_external': sorted(external), 'floor_gaps': gaps,
    'owned_modules': len(owned), 'owned_bytes': sum(r[k]['bytes'] for r in owned.values() for k in ['source','object']),
    'scope': 'Exact read-only dependency identity review. No new kernel proof credit and no relabeling of old incomplete external-floor replay.'}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2, sort_keys=True) + '\n')
print(json.dumps({k: v for k,v in review.items() if k != 'owned'}))
