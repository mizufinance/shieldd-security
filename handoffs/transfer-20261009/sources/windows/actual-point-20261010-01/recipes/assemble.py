"""Seal scoped actual point proofs, preserving failures and their zero credit."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
def pin(path):
    path = Path(path)
    with path.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
packet = ROOT / 'packet'; packet.mkdir(exist_ok=False)
def copy(path, relative):
    path = Path(path); dest = packet / relative
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(path, dest)
    assert pin(dest)['sha256'] == pin(path)['sha256']
tasks = ['transfer-torsion-cardinality49-20261010-03',
    'transfer-concrete-point-torsion-20261010-03',
    'transfer-concrete-point-doubling-20261010-02']
entries = []
for name in tasks:
    task = DIAG / name
    plan = json.loads((task / 'plan.json').read_text())
    events = [json.loads(x) for x in (task / 'events.jsonl').read_text().splitlines()]
    done = [e for e in events if e['event'] == 'attempt_finished']
    assert len(done) == len(plan['targets']) and all(e['result']['status'] == 'passed' for e in done)
    for file in ['plan.json', 'events.jsonl', 'prepare.py', 'execute_bounded.py']:
        copy(task / file, 'tasks/' + name + '/' + file)
    for e in done:
        target = next(t for t in plan['targets'] if t['module'] == e['module'])
        result = e['result']
        for r in [target['source'], result['stdout']] + result['objects']:
            assert pin(r['path']) == r
        assert len(result['audits']) == len(target['audit_names'])
        assert all(set(a['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in result['audits'].values())
        copy(target['source']['path'], 'handwritten-source/ShielddSecurity/' + e['module'] + '.lean')
        copy(result['stdout']['path'], 'audit-output/' + e['module'] + '.txt')
        entries.append({'module': e['module'], 'source': target['source'], 'task': name,
            'scope': plan['scope'], 'audit_pairs': len(result['audits']), 'receipt': result})
assert len(entries) == 5 and sum(e['audit_pairs'] for e in entries) == 33
failures = []
for name in ['transfer-concrete-point-torsion-20261010-01',
    'transfer-concrete-point-torsion-20261010-02', 'transfer-concrete-point-doubling-20261010-01']:
    task = DIAG / name
    files = ['plan.json', 'events.jsonl', 'prepare.py', 'execute_bounded.py']
    for file in files:
        copy(task / file, 'retained-failures/' + name + '/' + file)
    for source in (task / 'handwritten').glob('*.lean'):
        copy(source, 'retained-failures/' + name + '/' + source.name)
    for log in (task / 'runs').glob('*/stdout.txt'):
        copy(log, 'retained-failures/' + name + '/' + log.parent.name + '.txt')
    failures.append({'task': name, 'credit': 0,
        'classification': 'Failed elaboration or transient export-stat executor rejection; never semantic negative control.'})
for name in ['transfer-concrete-point-repair-recipe-20261010-01',
    'transfer-concrete-point-race-recipe-20261010-01', 'transfer-concrete-point-doubling-repair-20261010-01']:
    copy(DIAG / name / 'prepare.py', 'recipes/' + name + '.py')
copy(DIAG / 'transfer-actual-point-checkpoint-20261010-01/preservation.json', 'receipts/preservation.json')
copy(DIAG / 'transfer-actual-point-checkpoint-20261010-01/preservation_check.py', 'recipes/preservation_check.py')
field = DIAG / 'transfer-field-cardinality-endpoint-20261010-02'
copy(field / 'packet/manifest.json', 'inputs/field-cardinality-parent-manifest.json')
floor = DIAG / 'transfer-external-floor-complete-20261010-10/external-floor.json'
floor_data = json.loads(floor.read_text())
assert floor_data['admission_ready']
(packet / 'receipts/external-import-identities.json').write_text(json.dumps({
    'floor': pin(floor), 'first_package_composition': pin(DIAG / 'transfer-point-package-composed-20261010-01/composition-review.json'),
    'cache_qualification': pin(DIAG / 'transfer-point-cache-qualified-20261010-01/qualification.json'),
    'scope': 'Complete local official-reference comparisons and first-package selection. Transport hashes establish identity only; parent review is not a multi-gigabyte cache rehash or kernel replay.'}, indent=2) + '\n')
(packet / 'receipts/qualified-modules.json').write_text(json.dumps(entries, indent=2) + '\n')
copy(Path(__file__), 'recipes/assemble.py')
files = []
for path in sorted(packet.rglob('*')):
    if path.is_file():
        r = pin(path); r['path'] = path.relative_to(packet).as_posix(); files.append(r)
manifest = {'kind': 'SCOPED_WINDOWS_ACTUAL_POINT_BOUND_TWO_TORSION_AND_DOUBLING',
    'files': files, 'source_files': 5, 'type_axiom_pairs': 33, 'new_actual_point_pairs': 23,
    'modules': [{'module': e['module'], 'source_sha256': e['source']['sha256'], 'audit_pairs': e['audit_pairs']} for e in entries],
    'field_parent_archive': pin(field / 'portable-windows-field-cardinality-endpoint01.tar.xz'),
    'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'limits': {'threads': 1, 'heap_mib': 1536, 'heartbeats_at_most': 300000, 'recursion': 4096},
    'proof': 'Actual nonsingular Mathlib Point group over certified ZMod modulus. Finite full point set has at most2p+1 elements; two-torsion is zero or origin; origin has exact order2; kernel[8] has at most8 elements. Actual affine doubling outputs square X, so points at either certified nonsquare X firstX/secondX have no half. Three earlier symbolic torsion/cardinality ingredients included with their exact explicit premises.',
    'source_import_context': 'Previously transported 48-source field/cardinality parent packet plus accepted canonical source endpoints; host-specific replay plans pin the complete exact owned and external closure.',
    'retained_failures': failures,
    'open_obligations': ['Eight distinct kernel points and exhaustive order8 list', 'No order16',
        'Exact concrete base order binding', 'Full curve cardinality/global exponent',
        'Native admission and recovery correspondence', 'All original Transfer rows/copy conditions', 'Full Transfer'],
    'runtime_credit': 0, 'negative_control_credit': 0, 'certification_refresh': False,
    'complete_curve_cardinality': 'OPEN', 'native_correspondence': 'OPEN', 'full_transfer': 'OPEN', 'push_owner': 'parent'}
(packet / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
archive = ROOT / 'portable-windows-actual-point-endpoint01.tar.xz'
with tarfile.open(archive, 'w:xz', preset=9) as tar:
    for path in sorted(packet.rglob('*')):
        if not path.is_file(): continue
        data = path.read_bytes(); info = tarfile.TarInfo(path.relative_to(packet).as_posix())
        info.size = len(data); info.mtime = 0; info.mode = 0o644
        tar.addfile(info, io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 64*1024**2
print(json.dumps({'archive': pin(archive), 'manifest': pin(packet / 'manifest.json'),
    'files': len(files)+1, 'source_files': 5, 'type_axiom_pairs': 33, 'new_actual_point_pairs': 23}))
