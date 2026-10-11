"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-ordinary-storage-source-20261011-02'
CHECKPOINT = DIAG / 'transfer-ordinary-storage-checkpoint-20261011-01'
MODULE = 'TransferOrdinaryStorageSource01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-ordinary-storage-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 12 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 9 and len(pool['inherited_public_reports']) == 126
manager_endpoint = DIAG / 'transfer-current-volume-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-current-volume-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == '7c344cdaed324ac7e37fdc253deeb5e259a17f484eb27febdb997867962058b5'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-9-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 9 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
assert {**manager_pool['inherited_public_reports'], **manager_reports} == pool['inherited_public_reports']
manager_selected = manager_pool['selected'] + [{'module': 'TransferCurrentVolumeSource01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
for selected in pool['selected']:
    original = next(r for r in manager_selected if r['module'] == selected['module'])
    assert selected['source'] == original['source'] and selected['object'] == original['object']
    for k in ['source', 'object', 'copy']:
        assert pin(selected[k]['path']) == selected[k]
    carriers = [pin(manager_archive)]
    def collect_archive_refs(value):
        if isinstance(value, dict):
            if 'archive' in value and isinstance(value['archive'], dict) and 'path' in value['archive']:
                carriers.append(value['archive'])
            for nested in value.values():
                collect_archive_refs(nested)
        elif isinstance(value, list):
            for nested in value:
                collect_archive_refs(nested)
    collect_archive_refs(manager_reference)
    member = 'source/ShielddSecurity/' + selected['module'] + '.lean'
    found = False
    for carrier in {r['path']: r for r in carriers}.values():
        assert pin(carrier['path']) == carrier
        with tarfile.open(carrier['path'], 'r:xz') as tar:
            if member in tar.getnames():
                assert tar.extractfile(member).read() == Path(selected['source']['path']).read_bytes()
                found = True
                break
    assert found, selected['module']
assert manager_reference['ancestors']['ancestors']['ancestors']['core_floor']['original'] == plan['external_floor']
reference = {'current_volume': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'PARENT_REVIEW_ACCEPTED_AND_PUBLISHED_b124dc50bfc6f18b75557c70e61799cab17a90a8', 'imported_complete_reports': 9},
    'ancestors': manager_reference, 'complete_owned_modules': 9, 'inherited_complete_reports': 126,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact cache/raw/vector/batch/raw-effect/manager/SCT/framing/current-volume closure; capability and equality modules are not imported or replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'three both-callback executable definitions and nine finite Ordinary cache/read/write proofs')
add(stdout, 'reports/fresh-12-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete nine-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 126 inherited reports and exact source associations')
old = DIAG / 'transfer-ordinary-storage-source-20261011-01'
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
    add(row['path'], 'runtime/' + relative, 'exact pinned Ordinary payload/SCT/current-volume source; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'BOTH_SCT_CALLBACKS_DERIVE_ALL_RETURN_ORDINARY_CACHE_FRAMES_AND_SUCCESS_MARKERS_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 3, 'fresh_theorem_audits': 9,
    'fresh_complete_public_audits': 12, 'fresh_audits': fresh, 'inherited_complete_public_audits': 126,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 1, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' All three executable definitions and nine theorem contracts are unchanged from the failed attempt; successor proof annotations make the two reshape V/NV observations syntactically available at the installed backend alias and discharge a simplified True. Both markers persist after returned volume SCT/pending callback errors in this immutable model. Raw objects/events may remain altered. Successfully loaded immutable trees, actual getter panic, Clone/COW, key/value/event/source projections, tree and reader semantics, block finalization and durability remain explicit interfaces. Failed predecessor full zero credit.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-ordinary-storage-endpoint-v1', 'entries': records,
    'fresh_audits': 12, 'inherited_audits': 126, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 12, 'inherited_audits': 126,
    'native_test_credit': 0, 'certification': False}))
