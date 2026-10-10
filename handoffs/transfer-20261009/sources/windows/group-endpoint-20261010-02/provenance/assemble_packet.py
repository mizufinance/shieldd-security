"""Portable source and receipt capsule; no cache/object copying or certification refresh."""
import hashlib
import json
from pathlib import Path
import shutil
import io
import tarfile
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PACKET = ROOT / 'packet'
PACKET.mkdir(exist_ok=False)
records = []
def pin(p):
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
def copy(source, relative):
    source = Path(source)
    dest = PACKET / relative
    dest.parent.mkdir(parents=True, exist_ok=True)
    assert not dest.exists()
    shutil.copyfile(source, dest)
    original, result = pin(source), pin(dest)
    assert (original['bytes'], original['sha256']) == (result['bytes'], result['sha256'])
    records.append({'path': relative, 'bytes': result['bytes'], 'sha256': result['sha256'], 'original': original})
for phase, folder in [('prerequisites', 'transfer-floor-qualified-20261010-02'), ('group', 'transfer-group-qualified-20261010-02')]:
    receipt_path = DIAG / folder / 'qualification.json'
    receipt = json.loads(receipt_path.read_text())
    copy(receipt_path, 'receipts/' + phase + '-qualification.json')
    for q in receipt['qualified']:
        copy(q['source']['path'], 'sources/' + phase + '/ShielddSecurity/' + q['module'] + '.lean')
        copy(q['receipt']['stdout']['path'], 'audit-output/' + phase + '/' + q['module'] + '.txt')
for suffix in ['02', '03', '04']:
    task = DIAG / ('transfer-group-source47-20261010-' + suffix)
    for name in ['source-manifest.json', 'review.json', 'events.jsonl', 'repairs.json', 'generate_successors.py', 'generate_and_prepare.py']:
        path = task / name
        if path.exists(): copy(path, 'provenance/group-' + suffix + '/' + name)
copy(DIAG / 'transfer-prerequisite-floor-20261010-06' / 'execute_bounded.py', 'provenance/execute_bounded.py')
for phase, folder in [('prerequisites', 'transfer-prerequisite-floor-20261010-06'), ('group', 'transfer-group-source47-20261010-05')]:
    for name in ['plan.json', 'review.json', 'events.jsonl']:
        copy(DIAG / folder / name, 'provenance/corrected-' + phase + '/' + name)
for name in ['review_guards.py', 'guard-review.json']:
    copy(DIAG / 'transfer-prerequisite-floor-20261010-06' / name, 'provenance/corrected-admission/' + name)
copy(DIAG / 'transfer-external-floor-complete-20261010-01/withdrawal.json', 'provenance/withdrawn-packet-status.json')
copy(DIAG / 'transfer-external-floor-complete-20261010-02/inventory.py', 'provenance/complete-inventory-recipe.py')
copy(Path(__file__), 'provenance/assemble_packet.py')
inputs = DIAG / 'transfer-group-source47-20261010-01' / 'inputs' / 'packet'
copy(inputs / 'portable-source-manifest01.json', 'provenance/original-source47/portable-source-manifest01.json')
for source in (inputs / 'source-root' / 'ShielddSecurity').glob('*.lean'):
    copy(source, 'provenance/original-source47/ShielddSecurity/' + source.name)
for name in ['CompilerLinearCompletion', 'CompilerIndexed01']:
    copy(Path('C:/src/shieldd-formal/circuits/ShielddSecurity') / (name + '.lean'), 'provenance/original-source47/ShielddSecurity/' + name + '.lean')
manifest = {'schema': 'PORTABLE_WINDOWS_GROUP_ENDPOINT_20261010_02', 'files': records,
    'prerequisites': {'modules': 8, 'full_type_axiom_pairs': 44, 'qualification': 'fresh corrected complete-import rebuild passed', 'current_failed_attempts': 0},
    'group': {'modules': 8, 'full_type_axiom_pairs': 113, 'qualification': 'fresh corrected complete-import rebuild passed', 'current_failed_attempts': 0},
    'history': 'Prior failures and incomplete-import successes remain immutable observations. Original packet29c092d8c1143ebba6d1eff6f70de66c654a6968148358001d80f4c12d91afff is withdrawn for full import qualification. New receipts come only from fresh tasks06 andGroup05.',
    'source47_count_correction': 'The claimed85 Group declarations included prose inductive invariant.84 real Group declarations plus29 compiler declarations were audited.',
    'resource_limits': {'heap_mib': 1536, 'threads': 1, 'heartbeats_at_most': 300000, 'recursion': 4096, 'one_heavy_job_per_host': True},
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'mathlib_revision': 'c5ea00351c28e24afc9f0f84379aa41082b1188f',
    'external_floor': {'manifest_sha256': '1bd247c0fd30f52b01cb422bafe919df2818f3d953f4e088a44b226a0d1e04a2', 'manifest_bytes': 9575003, 'modules': 2802, 'files': 16151,
        'official_reference_sha256': '0a705f66a48b6c53041aa67139d477c1a9bb8e9166e794aa90c3538eb182f12d',
        'required_identity': 'Canonical package sources plusolean/private/server match official reference; optional hostir/ilean absent from reference are pinned auxiliaries. No semantic correspondence inferred from hashing.',
        'guards': 'Actual owned header equals planned imports; every direct external import and implicit Init must be in pinned recursive floor. Three read-only admission checks exercise the omissions before launch.'},
    'portability': 'Lean sources, audit outputs and sealed summaries are portable data. Recipe copies preserve provenance; original absolute-root recipes are not portable executable replay claims. No compiled objects or historical workspace/cache copied.',
    'global_curve_order': 'OPEN', 'native_correspondence': 'OPEN', 'full_transfer': 'OPEN', 'certification_refresh': False, 'negative_control_credit': 0}
(PACKET / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 8 * 1024**2
archive = ROOT / 'portable-windows-group-endpoint02.tar.xz'
with tarfile.open(archive, 'x:xz', preset=6) as bundle:
    for path in sorted(p for p in PACKET.rglob('*') if p.is_file()):
        data = path.read_bytes()
        info = tarfile.TarInfo(path.relative_to(PACKET).as_posix())
        info.size = len(data); info.mode = 0o644; info.mtime = 1791590400
        bundle.addfile(info, io.BytesIO(data))
with tarfile.open(archive, 'r:xz') as bundle:
    for r in records: assert hashlib.sha256(bundle.extractfile(r['path']).read()).hexdigest() == r['sha256']
seal = {'archive': pin(archive), 'manifest': pin(PACKET / 'manifest.json'), 'files': len(records) + 1,
    'all_retained_bytes': sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()), 'push_status': 'NOT_PUSHED; parent retains baton'}
(ROOT / 'seal.json').write_text(json.dumps(seal, indent=2) + '\n')
print(json.dumps(seal, indent=2))
