"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-writer-recovery-join-20261011-01'
CHECKPOINT = DIAG / 'transfer-writer-recovery-join-checkpoint-20261011-01'
MODULE = 'TransferWriterRecoveryJoin01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-writer-recovery-join-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 6 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 57 and len(pool['inherited_public_reports']) == 570
manager_endpoint = DIAG / 'transfer-authenticated-boundary-source-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-authenticated-boundary-source-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == '56d448763b1ca398393bd18d4249170924bc2dd56321f8558f8a41456908233c'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-9-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 9 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferAuthenticatedBoundarySource01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
legacy = DIAG / 'transfer-readback-recovery-publication-20261010-02'
legacy_endpoint = DIAG / 'transfer-readback-publication-endpoint-20261010-01'
legacy_archive = legacy_endpoint / 'portable-windows-readback-publication-endpoint01.tar.xz'
assert pin(legacy_archive)['sha256'] == '48b33b403223914e40cfedfd0d6031e68bde14fa5b659a72823caed344de47a8'
with tarfile.open(legacy_archive, 'r:xz') as tar:
    legacy_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    legacy_events = [json.loads(row) for row in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    bank_stdout = tar.extractfile('reports/TransferBankRecovery-complete-types-and-axioms.txt').read().decode()
    bank_source = tar.extractfile('source/ShielddSecurity/TransferBankRecovery.lean').read()
bank_target = next(row for row in legacy_plan['targets'] if row['module'] == 'TransferBankRecovery')
bank_result = next(row['result'] for row in legacy_events if row['event'] == 'attempt_finished' and row['module'] == 'TransferBankRecovery')
assert bank_result['status'] == 'passed'
bank_reports = m.audit(bank_stdout, bank_target['audit_names'])
assert len(bank_reports) == 10 and bank_reports == bank_result['audits']
assert bank_source == Path(bank_target['source']['path']).read_bytes()
assert bank_stdout.encode() == Path(bank_result['stdout']['path']).read_bytes()
shared_target = next(row for row in legacy_plan['targets'] if row['module'] == 'TransferReadback')
shared_result = next(row['result'] for row in legacy_events if row['event'] == 'attempt_finished' and row['module'] == 'TransferReadback')
shared_selected = next(row for row in manager_selected if row['module'] == 'TransferReadback')
assert shared_selected['source'] == shared_target['source'] and shared_selected['object'] == shared_result['objects'][0]
assert {name: combined_reports[name] for name in shared_target['audit_names']} == shared_result['audits']
assert set(combined_reports).isdisjoint(bank_reports)
combined_reports.update(bank_reports)
manager_selected.append({'module':'TransferBankRecovery','source':bank_target['source'],'object':bank_result['objects'][0]})
assert len(combined_reports) == 570 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 57
for selected in pool['selected']:
    original = next(r for r in manager_selected if r['module'] == selected['module'])
    assert selected['source'] == original['source'] and selected['object'] == original['object']
    for k in ['source', 'object', 'copy']:
        assert pin(selected[k]['path']) == selected[k]
    carriers = [pin(manager_archive), pin(legacy_archive)]
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
reference = {'authenticated_boundary_source': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 9},
    'ancestors': manager_reference, 'original_bank_recovery': {'archive':pin(legacy_archive), 'manifest':pin(legacy_endpoint / 'manifest.json'), 'selected_reports':10, 'source':bank_target['source'], 'object_identity':bank_result['objects'][0], 'shared_readback_17_reused_once':True, 'compiler_replay':False}, 'complete_owned_modules': 57, 'inherited_complete_reports': 570,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact fifty-seven-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging/keys/reader/authenticated snapshot/original recovery closure, with 570 original inherited complete reports; original BankRecovery10 imported without replay; shared StateDelta and seventeen Readback reports included once. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'source writer completion adapter to original qualified recovery model and four boundary/health/capacity/error composition proofs')
add(stdout, 'reports/fresh-6-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete fifty-seven-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 570 inherited reports and exact source associations')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
for name in ['plan.json', 'execute_bounded.py', 'events.jsonl', 'source-mapping.json', 'prepare.py', 'review.json', 'project/ShielddSecurity/TransferBankRecovery.lean', 'runs/02-TransferBankRecovery/stdout.txt']:
    add(legacy / name, 'original-BankRecovery/' + name, 'exact original independently qualified legacy source/runner/receipts/full reports; BankRecovery10 selected once, no replay or new native credit')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
runtime_rows = {row['path']: row for row in mapping['runtime_sources']}
for producer in ['transfer-nullifier-batch-source-20261011-02', 'transfer-raw-effects-source-20261011-04']:
    association_file = DIAG / producer / 'source-mapping.json'
    association_pin = pin(association_file)
    assert association_pin in plan['pins']
    association = json.loads(association_file.read_bytes())
    assert association['runtime_sha'] == mapping['runtime_sha']
    add(association_file, 'context/ancestor-source-associations/' + producer + '.json', 'unchanged source association already pinned in the qualified plan; not semantic proof')
    for row in association['runtime_sources']:
        assert pin(row['path']) == row
        assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
        runtime_rows[row['path']] = row
    for interface in association.get('interfaces', []):
        if interface not in mapping['interfaces']:
            mapping['interfaces'].append(interface)
mapping['runtime_sources'] = list(runtime_rows.values())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
    relative = Path(row['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(row['path'], 'runtime/' + relative, 'exact pinned Ordinary payload/SCT/current-volume source; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'SOURCE_WRITER_COMPLETION_ORIGINAL_RECOVERY_MODEL_JOIN_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 2, 'fresh_theorem_audits': 4,
    'fresh_complete_public_audits': 6, 'fresh_audits': fresh, 'inherited_complete_public_audits': 570,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 0, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' All six fresh declarations and original BankRecovery10 have complete original type/axiom reports. Shared Readback17 is unchanged and selected once. Native temporal state threading/current poison snapshots/partition frames/locks/IO/durability remain explicit rather than inferred from modeled adapter success. Recovery health stays independently observed; zero native/control/full certification credit.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-writer-recovery-join-endpoint-v1', 'entries': records,
    'fresh_audits': 6, 'inherited_audits': 570, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 6, 'inherited_audits': 570,
    'native_test_credit': 0, 'certification': False}))
