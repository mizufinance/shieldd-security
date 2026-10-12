"""Compose one first Mathlib root without copying the 3 GB external floor.

Directory junctions reference existing immutable directories; only thirteen exact
top-level NumberTheory object entries are new hardlinks (2.6 MB charged).
No prior input file or directory is changed. This is identity plumbing only.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
FLOOR = DIAG / 'transfer-external-floor-complete-20261010-06/external-floor.json'
ORIGINAL = DIAG / 'transfer-implementation-20261002/windows-jubjub-isolated-05/modules/Mathlib'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
floor = json.loads(FLOOR.read_text()); assert floor['admission_ready']
dest = ROOT / 'modules/Mathlib'; dest.mkdir(parents=True, exist_ok=False)
created = []; junctions = []
def junction(src, dst):
    src = src.resolve(); assert src.is_dir() and not dst.exists()
    assert dst.absolute().is_relative_to(ROOT)
    def quote(p): return "'" + str(p).replace("'", "''") + "'"
    cmd = 'New-Item -ItemType Junction -Path ' + quote(dst) + ' -Value ' + quote(src) + ' -ErrorAction Stop | Out-Null'
    subprocess.run(['powershell.exe', '-NoProfile', '-NonInteractive', '-Command', cmd], check=True, capture_output=True)
    assert dst.is_junction() and dst.resolve() == src
    junctions.append({'path': str(dst), 'existing_readonly_target': str(src)})
for src in ORIGINAL.iterdir():
    if src.is_dir() and src.name != 'NumberTheory': junction(src, dest / src.name)
nt = dest / 'NumberTheory'; nt.mkdir()
for src in (ORIGINAL / 'NumberTheory').iterdir():
    if src.is_dir(): junction(src, nt / src.name)
for module, item in floor['modules'].items():
    if (module.startswith('Mathlib.NumberTheory.') and module.count('.') == 2) or (module.startswith('Mathlib.') and module.count('.') == 1):
        for r in item['objects']:
            src = Path(r['path']); assert pin(src) == r
            dst = (dest if module.count(".") == 1 else nt) / src.name; assert not dst.exists()
            os.link(src, dst)
            record = pin(dst); assert record['sha256'] == r['sha256']
            created.append({'source': r, 'alias': record})
assert len(created) == 13 and sum(r['alias']['bytes'] for r in created) < 3 * 1024**2
assert 'Mathlib' not in floor['modules']
for r in created: assert pin(r['source']['path']) == r['source'] and pin(r['alias']['path']) == r['alias']
(ROOT / 'composition-review.json').write_text(json.dumps({'floor': pin(FLOOR), 'recipe': pin(Path(__file__)), 'junctions': junctions, 'created_hardlinks': created, 'charged_new_file_bytes': sum(r['alias']['bytes'] for r in created), 'limits': {'all_new_bytes': 64 * 1024**2, 'metadata_bytes': 16 * 1024**2}, 'scope': 'Fresh first-package root: existing immutable directory references plus thirteen new exact object hardlinks charged at full file size. No old cache changes, proof/native/control credit or resource escalation.'}, indent=2) + '\n')
print(json.dumps({'composition': pin(ROOT / 'composition-review.json'), 'modules_root': str(ROOT / 'modules'), 'charged_bytes': sum(r['alias']['bytes'] for r in created), 'junction_count': len(junctions)}))
