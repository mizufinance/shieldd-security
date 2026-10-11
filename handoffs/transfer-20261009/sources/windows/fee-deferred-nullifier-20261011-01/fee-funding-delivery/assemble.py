"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-fee-funding-delivery-20261011-03'
CHECKPOINT = DIAG / 'transfer-fee-funding-delivery-checkpoint-20261011-03'
MODULE = 'TransferFeeFundingDelivery01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-fee-funding-delivery-endpoint01.tar.xz'
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
assert pool['objects'] == 30 and len(pool['inherited_public_reports']) == 311
manager_endpoint = DIAG / 'transfer-deferred-max-count-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-deferred-max-count-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == 'ce328595c82ae0b19e85128606f2c17aac51f726659cda17786a70c3b0f2e638'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-3-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 3 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferDeferredMaxCount01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
assert len(combined_reports) == 311 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 30
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
reference = {'deferred_max_count': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'PARENT_ACCEPTED_9a80f89cb67879e3291c32508519fccb64ad608a', 'imported_complete_reports': 3},
    'ancestors': manager_reference, 'complete_owned_modules': 30, 'inherited_complete_reports': 311,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact thirty-module closure through concrete u64 current reads and complete Ordinary/deferred source joins, with all 311 inherited complete reports. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'FeeFunding source definition and three body/current-read/whole-delivery proofs')
add(stdout, 'reports/fresh-4-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete thirty-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 311 inherited reports and exact source associations')
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
review = {'status': 'FEE_FUNDING_WHOLE_DELIVERY_DERIVES_REEXTRACTION_CURRENT_READS_CODEC_AND_EFFECTS_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 1, 'fresh_theorem_audits': 3,
    'fresh_complete_public_audits': 4, 'fresh_audits': fresh, 'inherited_complete_public_audits': 311,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 2, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' One definition and all three theorems have complete original type/axiom reports. Both rejected predecessors remain immutable with zero whole-attempt credit. The proof-only successor closes the two True conjunctions and removes one unused simplification; all four contracts are unchanged. Native genuine controls remain separate and unrun.'}
dump(ROOT / 'review.json', review)
rejected = DIAG / 'transfer-fee-funding-delivery-20261011-01'
rejected_events = [json.loads(line) for line in (rejected / 'events.jsonl').read_text().splitlines()]
assert len(rejected_events) == 2 and rejected_events[-1]['result']['status'] == 'failed'
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json',
             'events.jsonl', 'handwritten/TransferFeeFundingDelivery01.lean', 'project/ShielddSecurity/TransferFeeFundingDelivery01.lean',
             'runs/01-TransferFeeFundingDelivery01/stdout.txt']:
    add(rejected / name, 'rejected-predecessor/' + name, 'immutable rejected whole attempt; zero proof credit')
import re
def contracts(text):
    return {match.group(1): match.group(0).split(' :=', 1)[0] for match in re.finditer(
        r'^(?:def|theorem) (\w+)[\s\S]*?(?=\n(?:def|theorem|set_option pp.all)|\Z)', text, re.M)}
original = (rejected / ('handwritten/' + MODULE + '.lean')).read_text()
successor = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
assert contracts(original) == contracts(successor) and len(contracts(original)) == 4
rejected_second = DIAG / 'transfer-fee-funding-delivery-20261011-02'
second_events = [json.loads(line) for line in (rejected_second / 'events.jsonl').read_text().splitlines()]
assert len(second_events) == 2 and second_events[-1]['result']['status'] == 'failed'
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json',
             'events.jsonl', 'handwritten/TransferFeeFundingDelivery01.lean', 'project/ShielddSecurity/TransferFeeFundingDelivery01.lean',
             'runs/01-TransferFeeFundingDelivery01/stdout.txt']:
    add(rejected_second / name, 'rejected-second-predecessor/' + name, 'immutable rejected second whole attempt; zero proof credit')
assert contracts(original) == contracts((rejected_second / ('handwritten/' + MODULE + '.lean')).read_text())
setup = DIAG / 'transfer-fee-funding-delivery-endpoint-20261011-02'
for name in ['prepare_assembly.py', 'assemble.py']:
    add(setup / name, 'unexecuted-assembly-setup/' + name, 'unexecuted predecessor sealer setup; no evidence or proof credit')
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-fee-funding-delivery-endpoint-v1', 'entries': records,
    'fresh_audits': 4, 'inherited_audits': 311, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 4, 'inherited_audits': 311,
    'native_test_credit': 0, 'certification': False}))
