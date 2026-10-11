"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-current-volume-source-20261011-02'
CHECKPOINT = DIAG / 'transfer-current-volume-checkpoint-20261011-01'
MODULE = 'TransferCurrentVolumeSource01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-current-volume-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 9 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 8 and len(pool['inherited_public_reports']) == 117
manager_endpoint = DIAG / 'transfer-raw-source-frames-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-raw-source-frames-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == '3623e7b32a7fb61bae9bfb85408e9686d0901361d3de6b16fc36b1220c9a32af'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-7-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 7 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
assert {**manager_pool['inherited_public_reports'], **manager_reports} == pool['inherited_public_reports']
manager_selected = manager_pool['selected'] + [{'module': 'TransferRawSourceFrames01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
for selected in pool['selected']:
    original = next(r for r in manager_selected if r['module'] == selected['module'])
    assert selected['source'] == original['source'] and selected['object'] == original['object']
    for k in ['source', 'object', 'copy']:
        assert pin(selected[k]['path']) == selected[k]
    if selected['module'] == 'TransferRawSourceFrames01':
        carrier = pin(manager_archive)
    elif selected['module'] == 'TransferSctInsertionSource01':
        carrier = manager_reference['sct']['archive']
    elif selected['module'] == 'TransferNoteManagerSource01':
        carrier = manager_reference['ancestors']['manager']['archive']
    else:
        tag = {'TransferStateDelta': 'raw', 'TransferRawStateProgram01': 'raw',
            'TransferNullifierReaderVector01': 'vector', 'TransferNullifierBatchSource01': 'batch',
            'TransferRawEffectsSource01': 'effects'}[selected['module']]
        carrier = manager_reference['ancestors']['ancestors'][tag]['archive']
    assert pin(carrier['path']) == carrier
    with tarfile.open(carrier['path'], 'r:xz') as tar:
        assert tar.extractfile('source/ShielddSecurity/' + selected['module'] + '.lean').read() == Path(selected['source']['path']).read_bytes()
assert manager_reference['ancestors']['ancestors']['core_floor']['original'] == plan['external_floor']
reference = {'framing': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'PARENT_REVIEW_ACCEPTED_AND_PUBLISHED_f6b0a8c5e1df4d2188d1f5e6ae31e9b3973ce822', 'imported_complete_reports': 7},
    'ancestors': manager_reference, 'complete_owned_modules': 8, 'inherited_complete_reports': 117,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact cache/raw/vector/batch/raw-effect/manager/SCT/framing closure; capability and equality modules are not imported or replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'four current-overlay executable definitions and five finite source-derived refusal proofs')
add(stdout, 'reports/fresh-9-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete eight-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 117 inherited reports and exact source associations')
old = DIAG / 'transfer-current-volume-source-20261011-01'
old_events = [json.loads(s) for s in (old / 'events.jsonl').read_text().splitlines()]
assert len(old_events) == 2 and old_events[-1]['result']['status'] == 'failed'
for name in ['prepare.py', 'prepare_recipe.py', 'plan.json', 'events.jsonl']:
    add(old / name, 'rejected/' + name, 'preserved original proof reduction rejection; zero credit')
add(old / ('handwritten/' + MODULE + '.lean'), 'rejected/source.lean', 'exact original rejected proof source')
add(old / ('runs/01-' + MODULE + '/stdout.txt'), 'rejected/compiler-output.txt', 'full compiler rejection; no proof or negative-control credit')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
    relative = Path(row['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(row['path'], 'runtime/' + relative, 'exact pinned current volume get_raw and layered cache source; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'SOURCE_DERIVED_CURRENT_OVERLAY_ORDINARY_REFUSAL_AND_DELIVERY_PRESERVATION_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 4, 'fresh_theorem_audits': 5,
    'fresh_complete_public_audits': 9, 'fresh_audits': fresh, 'inherited_complete_public_audits': 117,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 1, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'pre_admission_refused_cli': {'supplied_sha256': '00000000', 'lean_started': False, 'proof_credit': 0},
    'scope': mapping['scope'] + ' All four executable definitions and original refusal contracts are unchanged from the rejected attempt; the successor adds a small volume-tail lemma and stages rewrite observations before unfolding callback aliases. No successful reshape, desired read flag or rollback cache is a premise. Read errors remain distinct from absence and any present bytes imply spent. Original failed Lean and pre-admission invalid CLI receive zero credit.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-current-volume-endpoint-v1', 'entries': records,
    'fresh_audits': 9, 'inherited_audits': 117, 'inherited_reference': reference,
    'object_bytes_in_archive': 0, 'toolchain_bytes_in_archive': 0,
    'native_test_credit': 0, 'negative_control_credit': 0, 'certification': False, 'scope': review['scope']}
data = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
(ROOT / 'manifest.json').write_bytes(data)
payload.append(('manifest.json', data))
with tarfile.open(archive, 'w:xz', preset=6) as tar:
    for name, data in sorted(payload):
        info = tarfile.TarInfo(name)
        info.size, info.mode, info.mtime = len(data), 0o644, 0
        tar.addfile(info, io.BytesIO(data))
with tarfile.open(archive, 'r:xz') as tar:
    assert len(tar.getmembers()) == len(payload)
    assert all(tar.extractfile(name).read() == data for name, data in payload)
assert all(pin(r['original']['path']) == r['original'] for r in records)
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'), 'review': pin(ROOT / 'review.json'),
    'entries': len(records), 'members': len(payload), 'fresh_audits': 9, 'inherited_audits': 117,
    'native_test_credit': 0, 'certification': False}))
