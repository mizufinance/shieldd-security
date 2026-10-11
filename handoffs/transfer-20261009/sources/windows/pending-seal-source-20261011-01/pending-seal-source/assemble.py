"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-pending-seal-source-20261011-03'
CHECKPOINT = DIAG / 'transfer-pending-seal-source-checkpoint-20261011-03'
MODULE = 'TransferPendingSealSource01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-pending-seal-source-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 13 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 42 and len(pool['inherited_public_reports']) == 412
manager_endpoint = DIAG / 'transfer-block-pending-sequence-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-block-pending-sequence-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == '89d016ab7f8308d40fd4be280f98be78fa4b37fa341820cc4f068e20b022257d'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-10-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 10 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferBlockPendingSequence01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
assert len(combined_reports) == 412 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 42
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
reference = {'block_pending_sequence': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 10},
    'ancestors': manager_reference, 'complete_owned_modules': 42, 'inherited_complete_reports': 412,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact forty-two-module whole/current pending/durable reader/source capacity/global block uniqueness/order closure, with 412 original inherited complete reports; shared StateDelta and seventeen Readback reports included once. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'source enum/freeze/seal/ensure definitions and nine source/current-reader/frame/whole-staging refusal proofs')
add(stdout, 'reports/fresh-13-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete forty-two-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 412 inherited reports and exact source associations')
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
review = {'status': 'SOURCE_PENDING_ONE_SHOT_SEAL_FROZEN_ORDER_ENSURE_BRANCHES_AND_WHOLE_STAGE_REFUSAL_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 4, 'fresh_theorem_audits': 9,
    'fresh_complete_public_audits': 13, 'fresh_audits': fresh, 'inherited_complete_public_audits': 412,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 0, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' All four enum/definitions and nine theorems have complete original type/axiom reports. Current read and exact one-object/frame/ensure/repeated-error behavior are derived from source branches, and current Sealed excludes whole staging success. Native enum/Clone/typed/storage/owner correspondence and full certification remain separate; no native/control credit.'}
dump(ROOT / 'review.json', review)
import re
original = DIAG / 'transfer-pending-seal-source-20261011-01'
previous = DIAG / 'transfer-pending-seal-source-20261011-02'
original_source = (original / ('handwritten/' + MODULE + '.lean')).read_text()
previous_source = (previous / ('handwritten/' + MODULE + '.lean')).read_text()
new_source = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
assert re.sub(r'\bseal\b', 'sealOnce', original_source) == previous_source
old_proof = '  simp only [sealOnce, opened, Bool.false_eq_true, if_false]\n  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩'
new_proof = '''  have output : sealOnce encode decode objectKey child =
      ⟨(putObject child objectKey (some (encode (freeze (TransferCurrentPendingReplay01.currentPending decode objectKey child))))).cache, .ok ()⟩ := by
    simp only [sealOnce, opened, Bool.false_eq_true, if_false]
  rw [output]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩'''
assert previous_source.count(old_proof) == 1 and previous_source.replace(old_proof, new_proof) == new_source
rejected = []
for index, failed in enumerate([original, previous], 1):
    failed_events = [json.loads(line) for line in (failed / 'events.jsonl').read_text().splitlines()]
    assert len(failed_events) == 2 and failed_events[-1]['result']['status'] == 'failed'
    assert not (failed / ('project/ShielddSecurity/' + MODULE + '.olean')).exists()
    for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl',
        'handwritten/' + MODULE + '.lean', 'project/ShielddSecurity/' + MODULE + '.lean', 'runs/01-' + MODULE + '/stdout.txt']:
        assert pin(failed / name) in plan['pins']
        add(failed / name, 'rejected-%02d/' % index + name, 'failed parser/reflexive simplification predecessor; whole proof/control credit zero; immutable source/plan/diagnostics retained')
    rejected.append({'plan': pin(failed / 'plan.json'), 'compiler_result': failed_events[-1]['result'], 'proof_credit': 0, 'control_credit': 0})
for index in [1, 2]:
    stopped_sealer = DIAG / ('transfer-pending-seal-source-endpoint-20261011-%02d' % index)
    assert not (stopped_sealer / 'manifest.json').exists() and not (stopped_sealer / 'portable-windows-pending-seal-source-endpoint01.tar.xz').exists()
    for name in ['prepare_assembly.py', 'assemble.py']:
        add(stopped_sealer / name, 'unexecuted-sealer-%02d/' % index + name, 'unexecuted predecessor sealer setup, zero proof/control credit')
review['rejected_attempts'] = 2
review['rejected'] = rejected
review['successor_diff'] = '01 to 02 reserved helper name seal becomes sealOnce; 02 to 03 only opened-seal frame proof method changes to rewrite derived outcome before reflexive conjuncts. All thirteen contracts unchanged from 02, no premise/conclusion weakening or new axioms.'
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-pending-seal-source-endpoint-v1', 'entries': records,
    'fresh_audits': 13, 'inherited_audits': 412, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 13, 'inherited_audits': 412,
    'native_test_credit': 0, 'certification': False}))
