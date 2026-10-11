"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-deferred-count-walk-20261011-02'
CHECKPOINT = DIAG / 'transfer-deferred-count-walk-checkpoint-20261011-02'
MODULE = 'TransferDeferredCountWalk01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-deferred-count-walk-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 4 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 27 and len(pool['inherited_public_reports']) == 301
manager_endpoint = DIAG / 'transfer-ordinary-decodable-index-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-ordinary-decodable-index-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == '5ed12f0fa29459662b901786d2b3484e7c9b9651d33b2cddfb3a8492cde0f85d'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-1-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 1 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferOrdinaryDecodableIndex01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
deferred_endpoint = DIAG / 'transfer-deferred-queue-endpoint-20261010-01'
deferred_archive = deferred_endpoint / 'portable-windows-deferred-queue-endpoint01.tar.xz'
assert pin(deferred_archive)['sha256'] == 'eb830a8f56cd6927904dcf1564f4f53527863ab90dca0e8189f5c6c2ef250033'
with tarfile.open(deferred_archive, 'r:xz') as tar:
    deferred_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    deferred_events = [json.loads(x) for x in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    deferred_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    deferred_stdout = tar.extractfile('reports/fresh-17-complete-declarations.txt').read().decode()
deferred_reports = m.audit(deferred_stdout, deferred_plan['targets'][0]['audit_names'])
assert len(deferred_reports) == 17 and deferred_reports == deferred_events[-1]['result']['audits']
assert deferred_events[-1]['result']['status'] == 'passed'
assert set(deferred_reports).isdisjoint(combined_reports)
for name, report in deferred_pool['inherited_public_reports'].items():
    assert combined_reports[name] == report
for selected in deferred_pool['selected']:
    shared = next(r for r in manager_selected if r['module'] == selected['module'])
    assert shared['source'] == selected['source'] and shared['object'] == selected['object']
combined_reports.update(deferred_reports)
manager_selected.append({'module':'TransferDeferredQueueSourceModel01','source':deferred_plan['targets'][0]['source'],'object':deferred_events[-1]['result']['objects'][0]})

assert len(combined_reports) == 301 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 27
for selected in pool['selected']:
    original = next(r for r in manager_selected if r['module'] == selected['module'])
    assert selected['source'] == original['source'] and selected['object'] == original['object']
    for k in ['source', 'object', 'copy']:
        assert pin(selected[k]['path']) == selected[k]
    carriers = [pin(manager_archive), pin(deferred_archive)]
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
def core_floor_refs(value):
    if isinstance(value, dict):
        if 'core_floor' in value:
            yield value['core_floor']['original']
        for nested in value.values():
            yield from core_floor_refs(nested)
    elif isinstance(value, list):
        for nested in value:
            yield from core_floor_refs(nested)
assert plan['external_floor'] in list(core_floor_refs(manager_reference))
reference = {'whole_index_success': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 1},
    'deferred_walk': {'archive': pin(deferred_archive), 'manifest': pin(deferred_endpoint / 'manifest.json'), 'imported_complete_reports': 17, 'shared_complete_reports_not_recounted': 12},
    'ancestors': manager_reference, 'complete_owned_modules': 27, 'inherited_complete_reports': 301,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact twenty-seven-module merged closure: current concrete-codec index success plus deferred walk, with all 301 inherited complete reports and twelve shared state reports counted once. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'one current-overlay queue writer and three symbolic step/walk/count-bound proofs')
add(stdout, 'reports/fresh-4-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete twenty-seven-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 301 inherited reports and exact source associations')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
    relative = Path(row['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(row['path'], 'runtime/' + relative, 'exact pinned Ordinary payload/SCT/current-volume source; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
REJECTED = DIAG / 'transfer-deferred-count-walk-20261011-01'
history = [json.loads(x) for x in (REJECTED / 'events.jsonl').read_text().splitlines()]
assert len(history) == 2 and history[-1]['result']['status'] == 'failed'
import re
old = (REJECTED / ('handwritten/' + MODULE + '.lean')).read_text()
new = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
def signatures(text):
    return [text[match.start():text.index(' :=',match.start())] for match in re.finditer(r'^theorem ',text,re.M)]
assert signatures(old) == signatures(new) and len(signatures(new)) == 3
assert old[old.index('def queueWriter'):old.index('theorem ')] == new[new.index('def queueWriter'):new.index('theorem ')]
for name in ['prepare.py','prepare_recipe.py','plan.json','review.json','source-mapping.json','events.jsonl','execute_bounded.py','handwritten/' + MODULE + '.lean','project/ShielddSecurity/' + MODULE + '.lean','runs/01-' + MODULE + '/stdout.txt']:
    add(REJECTED / name, 'rejected-01/' + name, 'original compiler failure; whole attempt zero credit')
for name in ['prepare-rejected-owned-count.py','prepare_recipe-rejected-owned-count.py']:
    add(REJECTED / name, 'rejected-preparation/' + name, 'owned census correction before plan or Lean admission; zero proof credit')

add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'ARBITRARY_DEFERRED_WALK_DERIVES_COUNT_INCREASE_WITHOUT_U64_WRAP_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 1, 'fresh_theorem_audits': 3,
    'fresh_complete_public_audits': 4, 'fresh_audits': fresh, 'inherited_complete_public_audits': 301,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 1, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' Successful fresh successor supplies all four complete original type/axiom reports. One queue-writer definition and three theorem conclusions are unchanged; only overlay normalization in the step proof was repaired. Rejected compiler attempt receives zero credit. Both exact inherited source/object/report branches were checked, with all twelve shared state reports equal and counted once. The earlier preparation stopped before Lean because its expected owned census omitted one imported module; the corrected census is27, with guards and theorem contracts unchanged and zero preparation credit. Native queued genuine-control execution remains separate and unrun.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-deferred-count-walk-endpoint-v1', 'entries': records,
    'fresh_audits': 4, 'inherited_audits': 301, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 4, 'inherited_audits': 301,
    'native_test_credit': 0, 'certification': False}))
