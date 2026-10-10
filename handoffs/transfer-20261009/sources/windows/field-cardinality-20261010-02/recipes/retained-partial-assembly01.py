"""Seal qualified finite field/cardinality ingredients only; refuse partial trees."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent

def pin(p):
    p = Path(p)
    with p.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}

packet = ROOT / 'packet'
packet.mkdir(exist_ok=False)

def copy(p, relative):
    p = Path(p)
    dest = packet / relative
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(p, dest)
    assert pin(dest)['sha256'] == pin(p)['sha256']

tasks = ['transfer-modular-power-field-20261010-01'] + [
    'transfer-prime-tree-closed-20261010-%02d' % n for n in range(1, 6)] + [
    'transfer-torsion-prime-nonsquare-20261010-04',
    'transfer-cardinality-image-20261010-02',
    'transfer-torsion-odd-image-20261010-03',
    'transfer-affine-fibre-bound-20261010-03',
    'transfer-doubling-kernel-bound-20261010-04',
    'transfer-torsion-certified-field-20261010-01']
entries = []
for name in tasks:
    task = DIAG / name
    plan = json.loads((task / 'plan.json').read_text())
    events = [json.loads(x) for x in (task / 'events.jsonl').read_text().splitlines()]
    done = [e for e in events if e['event'] == 'attempt_finished']
    assert len(done) == len(plan['targets']) and all(e['result']['status'] == 'passed' for e in done), name
    copy(task / 'plan.json', 'plans/' + name + '.json')
    copy(task / 'events.jsonl', 'events/' + name + '.jsonl')
    copy(task / 'prepare.py', 'recipes/' + name + '/prepare.py')
    for e in done:
        result = e['result']
        target = next(t for t in plan['targets'] if t['module'] == e['module'])
        for r in [target['source'], result['stdout']] + result['objects']:
            assert pin(r['path']) == r
        assert len(result['audits']) == len(target['audit_names'])
        module = e['module']
        generated = module.startswith('FieldPrimeNode')
        copy(target['source']['path'], ('generated-source' if generated else 'handwritten-source') + '/ShielddSecurity/' + module + '.lean')
        copy(result['stdout']['path'], 'audit-output/' + module + '.txt')
        entries.append({'module': module, 'source': target['source'], 'audit_pairs': len(result['audits']), 'receipt': result, 'task': name, 'scope': plan['scope']})
assert len(entries) == 48 and sum(e['audit_pairs'] for e in entries) == 167
assert [e['module'] for e in entries if e['module'].startswith('FieldPrimeNode')] == ['FieldPrimeNode%02d' % n for n in range(1, 39)]
copy(DIAG / 'transfer-prerequisite-floor-20261010-06/execute_bounded.py', 'recipes/execute_bounded.py')
for relative in ['generation-review.json', 'prepare.py', 'replay_original_generator.py']:
    copy(DIAG / 'transfer-prime-tree-replay-20261010-02' / relative, 'recipes/prime-tree/' + relative)
copy(Path('C:/src/shieldd-transfer-windows-publication-20261009/handoffs/transfer-20261009/sources/parent/field-certificate-inputs01/candidate.json'), 'inputs/prime-candidate.json')

failures = []
for name in ['transfer-torsion-prime-nonsquare-20261010-01', 'transfer-torsion-prime-nonsquare-20261010-02',
             'transfer-torsion-prime-nonsquare-20261010-03', 'transfer-affine-fibre-bound-20261010-01',
             'transfer-affine-fibre-bound-20261010-02', 'transfer-doubling-kernel-bound-20261010-02']:
    task = DIAG / name
    record = {'task': name, 'credit': 0, 'classification': 'Failed build/preflight; never a semantic negative control.'}
    for file in ['plan.json', 'events.jsonl']:
        if (task / file).is_file():
            record[file] = pin(task / file)
            copy(task / file, 'retained-failures/' + name + '/' + file)
    for source in (task / 'handwritten').glob('*.lean'):
        copy(source, 'retained-failures/' + name + '/' + source.name)
    for log in (task / 'runs').glob('*/stdout.txt'):
        copy(log, 'retained-failures/' + name + '/' + log.parent.name + '.txt')
    failures.append(record)
(packet / 'retained-failures/summary.json').write_text(json.dumps(failures, indent=2) + '\n')
copy(DIAG / 'transfer-field-cardinality-checkpoint-20261010-02/preservation.json', 'receipts/preservation.json')
inventory_records = [pin(DIAG / ('transfer-external-floor-complete-20261010-%02d' % n) / 'external-floor.json') for n in [4, 8, 9]]
(packet / 'receipts/import-inventory-identities.json').write_text(json.dumps({
    'inventories': inventory_records,
    'first_package_composition': pin(DIAG / 'transfer-external-package-overlay-20261010-03/composition-review.json'),
    'scope': 'Complete local import inventories and exact official-reference comparisons remain local immutable inputs. Hashes establish identity; parent transport/review does not assert rehashing the multi-gigabyte cache or kernel replay.'}, indent=2) + '\n')
(packet / 'receipts/qualified-modules.json').write_text(json.dumps(entries, indent=2) + '\n')
files = []
for path in sorted(packet.rglob('*')):
    if path.is_file():
        record = pin(path)
        record['path'] = path.relative_to(packet).as_posix()
        files.append(record)
manifest = {'kind': 'SCOPED_WINDOWS_CERTIFIED_FIELD_AND_CARDINALITY_INGREDIENTS', 'files': files,
    'source_files': 48, 'type_axiom_pairs': 167,
    'modules': [{'module': e['module'], 'source_sha256': e['source']['sha256'], 'audit_pairs': e['audit_pairs']} for e in entries],
    'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'limits': {'threads': 1, 'heap_mib': 1536, 'heartbeats_at_most': 300000, 'recursion': 4096, 'max_named_modules_per_task': 8},
    'proof': 'Exact original generator/candidate replay closes all38 Lucas nodes and the actual modulus prime. Binary modular recurrence soundness and actual ZMod Euler residues yield three nonsquares without an assumed PrimeFact in the certified-field conclusions. Separate generic finite-group kernel/image/cardinality, Cauchy odd-image, square-fibre counting and symbolic doubling-kernel recurrence remain conditional on their explicit group/curve premises.',
    'open_obligations': ['Actual concrete Point bindings', 'Concrete two-torsion classification', 'Eight-point lower bound/exhaustive torsion', 'No order sixteen', 'Concrete base point order', 'Full curve cardinality', 'Native correspondence', 'All Transfer row instances', 'Full Transfer'],
    'retained_failures': failures,
    'complete_curve_cardinality': 'OPEN', 'native_correspondence': 'OPEN', 'full_transfer': 'OPEN',
    'runtime_credit': 0, 'negative_control_credit': 0, 'certification_refresh': False, 'push_owner': 'parent',
    'recipes': 'Construction provenance with host-specific paths; no claim of a portable closed replay. Caches/objects/toolchains and composed runtime workspaces excluded.'}
(packet / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
archive = ROOT / 'portable-windows-field-cardinality-endpoint01.tar.xz'
with tarfile.open(archive, 'w:xz', preset=9) as tar:
    for path in sorted(packet.rglob('*')):
        if not path.is_file():
            continue
        data = path.read_bytes()
        info = tarfile.TarInfo(path.relative_to(packet).as_posix())
        info.size = len(data); info.mtime = 0; info.mode = 0o644
        tar.addfile(info, io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 64 * 1024**2
print(json.dumps({'archive': pin(archive), 'manifest': pin(packet / 'manifest.json'), 'files': len(files) + 1, 'modules': 48, 'audit_pairs': 167}))
