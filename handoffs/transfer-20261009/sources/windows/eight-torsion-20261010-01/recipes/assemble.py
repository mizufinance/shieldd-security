"""Seal actual eight-torsion enumeration and no16, retaining all failed predecessors."""
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
tasks = ['transfer-concrete-point-coordinate-20261010-01', 'transfer-concrete-eight-data-20261010-01',
    'transfer-concrete-eight-witness-20261010-02', 'transfer-concrete-no-sixteen-20261010-02']
entries = []
for name in tasks:
    task = DIAG / name
    plan = json.loads((task / 'plan.json').read_text())
    events = [json.loads(x) for x in (task / 'events.jsonl').read_text().splitlines()]
    done = [e for e in events if e['event'] == 'attempt_finished']
    assert len(done) == len(plan['targets']) == 1 and done[0]['result']['status'] == 'passed'
    for file in ['plan.json', 'events.jsonl', 'prepare.py', 'execute_bounded.py']:
        copy(task / file, 'tasks/' + name + '/' + file)
    for e in done:
        target = next(t for t in plan['targets'] if t['module'] == e['module'])
        result = e['result']
        for r in [target['source'], result['stdout']] + result['objects']: assert pin(r['path']) == r
        assert len(result['audits']) == len(target['audit_names'])
        assert all(set(a['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in result['audits'].values())
        kind = 'generated-source' if e['module'] == 'ConcreteEightTorsionData01' else 'handwritten-source'
        copy(target['source']['path'], kind + '/ShielddSecurity/' + e['module'] + '.lean')
        copy(result['stdout']['path'], 'audit-output/' + e['module'] + '.txt')
        entries.append({'module': e['module'], 'source': target['source'], 'task': name,
            'scope': plan['scope'], 'audit_pairs': len(result['audits']), 'receipt': result})
    for file in ['prepare_source.py', 'prepare_recipe.py', 'generate.py', 'generation-review.json']:
        if (task / file).exists(): copy(task / file, 'recipes/' + name + '-' + file)
assert len(entries) == 4 and sum(e['audit_pairs'] for e in entries) == 39
failures = []
for name in ['transfer-concrete-eight-witness-20261010-01', 'transfer-concrete-no-sixteen-20261010-01']:
    task = DIAG / name
    for file in ['plan.json', 'events.jsonl', 'prepare.py', 'prepare_recipe.py', 'execute_bounded.py']:
        copy(task / file, 'retained-failures/' + name + '/' + file)
    for source in (task / 'handwritten').glob('*.lean'): copy(source, 'retained-failures/' + name + '/' + source.name)
    for log in (task / 'runs').glob('*/stdout.txt'): copy(log, 'retained-failures/' + name + '/' + log.parent.name + '.txt')
    failures.append({'task': name, 'credit': 0, 'classification': 'Failed elaboration; never a semantic negative control.'})
copy(DIAG / 'transfer-torsion-cardinality49-20261010-01/inputs/candidates49-DATA.json', 'inputs/candidates49-DATA.json')
check = DIAG / 'transfer-eight-torsion-checkpoint-20261010-01'
copy(check / 'preservation.json', 'receipts/preservation.json')
copy(check / 'preservation_check.py', 'recipes/preservation_check.py')
parent = DIAG / 'transfer-actual-point-endpoint-20261010-01'
field = DIAG / 'transfer-field-cardinality-endpoint-20261010-02'
copy(parent / 'packet/manifest.json', 'inputs/actual-point-parent-manifest.json')
copy(field / 'packet/manifest.json', 'inputs/field-cardinality-parent-manifest.json')
floor = DIAG / 'transfer-external-floor-complete-20261010-10/external-floor.json'
assert json.loads(floor.read_text())['admission_ready']
(packet / 'receipts/external-import-identities.json').write_text(json.dumps({
    'floor': pin(floor), 'first_package_composition': pin(DIAG / 'transfer-point-package-composed-20261010-01/composition-review.json'),
    'cache_qualification': pin(DIAG / 'transfer-point-cache-qualified-20261010-01/qualification.json'),
    'scope': 'Complete local external closure and first package selection. Transport identity does not imply parent cache rehash or kernel replay.'}, indent=2) + '\n')
(packet / 'receipts/qualified-modules.json').write_text(json.dumps(entries, indent=2) + '\n')
copy(Path(__file__), 'recipes/assemble.py')
files = []
for path in sorted(packet.rglob('*')):
    if path.is_file():
        r = pin(path); r['path'] = path.relative_to(packet).as_posix(); files.append(r)
manifest = {'kind': 'SCOPED_WINDOWS_ACTUAL_EIGHT_TORSION_EXHAUSTIVE_AND_NO_SIXTEEN',
    'files': files, 'source_files': 4, 'handwritten_sources': 3, 'generated_sources': 1, 'type_axiom_pairs': 39,
    'modules': [{'module': e['module'], 'source_sha256': e['source']['sha256'], 'audit_pairs': e['audit_pairs']} for e in entries],
    'actual_point_parent_archive': pin(parent / 'portable-windows-actual-point-endpoint01.tar.xz'),
    'field_parent_archive': pin(field / 'portable-windows-field-cardinality-endpoint01.tar.xz'),
    'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'canonical_parent_sha': '494583e09ce43f8ec23d48253815f9adc15fc10a',
    'limits': {'threads': 1, 'heap_mib': 1536, 'heartbeats_at_most': 300000, 'recursion': 4096},
    'proof': 'Exact integer congruence certificates imply actual three-point coordinate equations and doubles/add. Concrete point1 has exact order8; Fin8 multiples exhaust the actual eight-multiplication kernel, whose cardinality is8. Every actual order8 point is an odd multiple. Established nonsquare first/third coordinates exclude its halves; there is no actual point of order16, and Cauchy implies an odd eight-multiplication image.',
    'source_import_context': 'Separately reviewed exact actual-point and field/cardinality parent manifests plus accepted canonical dependencies. Local named plans pin complete owned imports and external floor.',
    'retained_failures': failures,
    'open_obligations': ['Exact concrete base order binding', 'Full curve cardinality/global exponent', 'Native admission and recovery correspondence', 'All original Transfer rows/copy conditions', 'Full Transfer'],
    'runtime_credit': 0, 'negative_control_credit': 0, 'certification_refresh': False,
    'complete_curve_cardinality': 'OPEN', 'native_correspondence': 'OPEN', 'full_transfer': 'OPEN', 'push_owner': 'parent'}
(packet / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
archive = ROOT / 'portable-windows-eight-torsion-endpoint01.tar.xz'
with tarfile.open(archive, 'w:xz', preset=9) as tar:
    for path in sorted(packet.rglob('*')):
        if not path.is_file(): continue
        data = path.read_bytes(); info = tarfile.TarInfo(path.relative_to(packet).as_posix())
        info.size = len(data); info.mtime = 0; info.mode = 0o644
        tar.addfile(info, io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 64*1024**2
print(json.dumps({'archive': pin(archive), 'manifest': pin(packet / 'manifest.json'), 'files': len(files)+1, 'source_files': 4, 'type_axiom_pairs': 39}))
