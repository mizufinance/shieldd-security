"""Finite, read-only official-cache lookup for exactly 78 new external imports."""
import hashlib
import json
from pathlib import Path
import os
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
MAIN = Path('C:/src/shieldd-formal')
ML = MAIN / 'circuits/.lake/packages/mathlib'
T = Path('C:/Users/acyrn/.elan/toolchains/leanprover--lean4---v4.30.0')
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
old_path = DIAG / 'transfer-external-floor-complete-20261010-01/external-floor.json'
floor_path = DIAG / 'transfer-external-floor-complete-20261010-02/external-floor.json'
old = json.loads(old_path.read_text())
floor = json.loads(floor_path.read_text())
modules = sorted(set(old['modules']) - set(floor['modules']))
assert len(modules) == 78
pins = [pin(old_path), pin(floor_path), pin(Path(__file__)),
    pin(ROOT / 'execute_metadata.py'),
    pin(DIAG / 'transfer-prerequisite-floor-20261010-06/execute_bounded.py')]
pins += [pin(ML / p) for p in ['.lake/build/bin/cache.exe', 'Cache/Main.lean',
    'Cache/IO.lean', 'Cache/Hashing.lean', 'Cache/Requests.lean',
    'lakefile.lean', 'lake-manifest.json', 'lean-toolchain']]
pins += [pin(T / 'bin' / p) for p in ['lean.exe', 'leantar.exe']]
pins += [old['modules'][m]['source'] for m in modules]
plan = {'kind': 'READ_ONLY_CACHE_HASH_AND_EMBEDDED_COMMIT_LOOKUP',
    'host': os.environ['COMPUTERNAME'], 'modules': modules, 'pins': pins,
    'command': [str(ML / '.lake/build/bin/cache.exe'), 'lookup'] + modules,
    'cwd': str(ML), 'toolchain_bin': str(T / 'bin'),
    'source_path': [str(p) for p in (MAIN / 'circuits/.lake/packages').iterdir() if p.is_dir()] + [str(T / 'src/lean')],
    'cache_dir': 'C:/Users/acyrn/.cache/mathlib',
    'limits': {'seconds': 120, 'active_processes': 2, 'job_memory_bytes': 4 * 1024**3,
        'output_bytes': 1024**2, 'all_new_bytes': 64 * 1024**2, 'metadata_bytes': 16 * 1024**2},
    'scope': 'No download, unpack, build, Lake, native Shieldd execution or proof. cache.exe initializes with lean --print-prefix and calls bundled leantar -k sequentially. Existing inputs remain read-only. Output is identity/provenance metadata only; zero theorem/runtime/negative-control credit.'}
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'modules': len(modules), 'credit': 0}))
