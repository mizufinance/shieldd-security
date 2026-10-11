"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-whole-durable-readback-20261011-02'
CHECKPOINT = DIAG / 'transfer-whole-durable-readback-checkpoint-20261011-02'
MODULE = 'TransferWholeDurableReadback01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-whole-durable-readback-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 11 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 37 and len(pool['inherited_public_reports']) == 368
manager_endpoint = DIAG / 'transfer-current-pending-replay-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-current-pending-replay-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == '23484b471486055e5bc1f0c2a754fa4b135ac415d272c6f1868606a3e2128b1d'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-8-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 8 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferCurrentPendingReplay01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
assert len(combined_reports) == 351
readback_endpoint = DIAG / 'transfer-readback-publication-endpoint-20261010-01'
readback_archive = readback_endpoint / 'portable-windows-readback-publication-endpoint01.tar.xz'
assert pin(readback_archive)['sha256'] == '48b33b403223914e40cfedfd0d6031e68bde14fa5b659a72823caed344de47a8'
assert pin(readback_archive) in plan['pins']
with tarfile.open(readback_archive, 'r:xz') as tar:
    readback_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    readback_events = [json.loads(line) for line in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    readback_stdout = tar.extractfile('reports/TransferReadback-complete-types-and-axioms.txt').read().decode()
    readback_reports = m.audit(readback_stdout, readback_plan['targets'][0]['audit_names'])
assert len(readback_reports) == 17 and readback_reports == readback_events[1]['result']['audits']
assert set(combined_reports).isdisjoint(readback_reports)
combined_reports.update(readback_reports)
manager_selected.append({'module': 'TransferReadback', 'source': readback_plan['targets'][0]['source'],
    'object': readback_events[1]['result']['objects'][0]})
assert len(combined_reports) == 368 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 37
for selected in pool['selected']:
    original = next(r for r in manager_selected if r['module'] == selected['module'])
    assert selected['source'] == original['source'] and selected['object'] == original['object']
    for k in ['source', 'object', 'copy']:
        assert pin(selected[k]['path']) == selected[k]
    carriers = [pin(manager_archive), pin(readback_archive)]
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
reference = {'current_pending_replay': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 8},
    'readback': {'archive': pin(readback_archive), 'manifest': pin(readback_endpoint / 'manifest.json'), 'imported_complete_reports': 17, 'scope': 'Exactly the original Readback source/object and seventeen full reports are reused; BankRecovery/WriterPublication modules are not imported by this join.'},
    'ancestors': manager_reference, 'complete_owned_modules': 37, 'inherited_complete_reports': 368,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact thirty-seven-module closure joining whole body/current pending/source-key proofs to the original durable Readback model, with 368 inherited complete reports. Readback has no owned imports; shared StateDelta appears once. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'current typed Reader/boundary/lock/verified status and whole-delivery conditional authenticated absence')
add(stdout, 'reports/fresh-11-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete thirty-seven-module first import root; no object bytes')
add(DIAG / 'transfer-readback-recovery-publication-20261010-02/source-mapping.json', 'context/readback-source-association.json', 'exact old source association already pinned; semantic/native/codec/Merkle interfaces remain explicit')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 368 inherited reports and exact source associations')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
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
review = {'status': 'WHOLE_TRANSFER_SUCCESS_DERIVES_VERIFIED_DURABLE_READBACK_AND_CONDITIONAL_AUTHENTICATED_ABSENCE_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 3, 'fresh_theorem_audits': 8,
    'fresh_complete_public_audits': 11, 'fresh_audits': fresh, 'inherited_complete_public_audits': 368,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 0, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' All three definitions and eight theorems have complete original type/axiom reports. Exactly seventeen old Readback reports are re-audited and source/object identities verified from the already accepted archive. No old Lean module or native control is replayed; no full Transfer certification credit.'}
dump(ROOT / 'review.json', review)
failed = DIAG / 'transfer-whole-durable-readback-20261011-01'
failed_plan = json.loads((failed / 'plan.json').read_bytes())
failed_events = [json.loads(line) for line in (failed / 'events.jsonl').read_text().splitlines()]
assert len(failed_events) == 2 and failed_events[-1]['result']['status'] == 'failed'
assert not (failed / ('project/ShielddSecurity/' + MODULE + '.olean')).exists()
old_source = (failed / ('handwritten/' + MODULE + '.lean')).read_text()
new_source = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
expected = old_source.replace('exact ⟨store, boundary, response, reader, boundaryRead, locked, checked, unspent⟩',
    'exact ⟨store, boundary, response, rfl, rfl, rfl, checked, unspent⟩')
expected = expected.replace('∃ store boundary response,', '∃ (store : Store) (boundary : Boundary) (response : Status),')
assert expected == new_source
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl',
    'handwritten/' + MODULE + '.lean', 'project/ShielddSecurity/' + MODULE + '.lean', 'runs/01-' + MODULE + '/stdout.txt']:
    row = pin(failed / name)
    assert row in plan['pins']
    add(failed / name, 'rejected-01/' + name, 'failed elaboration predecessor, whole proof/control credit zero; no admitted source mutated')
stopped_sealer = DIAG / 'transfer-whole-durable-readback-endpoint-20261011-01'
assert not (stopped_sealer / 'manifest.json').exists() and not (stopped_sealer / 'portable-windows-whole-durable-readback-endpoint01.tar.xz').exists()
for name in ['prepare_assembly.py', 'assemble.py']:
    add(stopped_sealer / name, 'unexecuted-sealer-01/' + name, 'unexecuted predecessor sealer setup, zero proof/control credit')
readback = DIAG / 'transfer-readback-recovery-publication-20261010-02'
for name in ['project/ShielddSecurity/TransferReadback.lean', 'plan.json', 'execute_bounded.py', 'events.jsonl',
    'source-mapping.json', 'runs/01-TransferReadback/stdout.txt']:
    row = pin(readback / name)
    assert row in plan['pins']
    add(readback / name, 'readback-ancestor/' + name, 'original seventeen-report Readback source/plan/runner/events/raw type and axiom association; no replay credit')
assert pin(readback / 'project/ShielddSecurity/TransferReadback.olean') == readback_events[1]['result']['objects'][0]
review['rejected_attempts'] = 1
review['rejected_attempt'] = {'plan': pin(failed / 'plan.json'), 'compiler_result': failed_events[-1]['result'],
    'proof_credit': 0, 'control_credit': 0, 'successor_diff': 'Only reflexivity for rewritten case goals and explicit intended Store/Boundary/Status existential type annotations; no premises or conclusions weakened.'}
review['readback_ancestor'] = {'module': 'TransferReadback', 'source': readback_plan['targets'][0]['source'],
    'object': readback_events[1]['result']['objects'][0], 'stdout': readback_events[1]['result']['stdout'], 'complete_reports': 17,
    'archive': pin(readback_archive), 'transport': 'windows-readback-publication-endpoint01', 'fresh_replay_credit': 0}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-whole-durable-readback-endpoint-v1', 'entries': records,
    'fresh_audits': 11, 'inherited_audits': 368, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 11, 'inherited_audits': 368,
    'native_test_credit': 0, 'certification': False}))
