"""Resolve the newly composed first Mathlib package root and pin every alias."""
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
OLD = DIAG / 'transfer-external-floor-complete-20261010-06/external-floor.json'
OVERLAY = DIAG / 'transfer-external-package-overlay-20261010-03'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
review = json.loads((OVERLAY / 'composition-review.json').read_text())
for r in review['created_hardlinks']:
    assert pin(r['source']['path']) == r['source'] and pin(r['alias']['path']) == r['alias']
for j in review['junctions']:
    assert Path(j['path']).is_junction() and Path(j['path']).resolve() == Path(j['existing_readonly_target'])
d = json.loads(OLD.read_text()); assert d['admission_ready']
for module, item in d['modules'].items():
    if not module.startswith('Mathlib.'): continue
    for i, record in enumerate(item['objects']):
        alias = OVERLAY / 'modules' / (module.replace('.', '/') + Path(record['path']).name[len(module.split('.')[-1]):])
        actual = pin(alias)
        assert actual['sha256'] == record['sha256'] and actual['bytes'] == record['bytes']
        # A directory reference resolves to the original path. New direct object
        # hardlinks retain the fresh alias path and are explicitly pinned there.
        if alias.resolve() != Path(record['path']).resolve(): item['objects'][i] = actual
        chosen = OVERLAY / 'modules' / (module.replace('.', '/') + '.olean')
        required = next(r for r in item['objects'] if r['path'].endswith('.olean'))
        assert chosen.resolve() == Path(required['path']).resolve()
files = {}
for item in d['modules'].values():
    for r in [item['source']] + item['objects']: files[r['path']] = r
d['immutable_files'] = list(files.values())
d['first_package_composition'] = pin(OVERLAY / 'composition-review.json')
d['scope'] += ' Fresh exact first Mathlib package root references immutable directory targets and pins newly charged direct object aliases; source identities and original object identities unchanged.'
(ROOT / 'external-floor.json').write_text(json.dumps(d, indent=2, sort_keys=True) + '\n')
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 16 * 1024**2
print(json.dumps({'inventory': pin(ROOT / 'external-floor.json'), 'modules': len(d['modules']), 'files': len(files), 'admission_ready': True}))
