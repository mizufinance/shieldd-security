"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-word-object-put-20261011-03'
CHECKPOINT = DIAG / 'transfer-word-object-put-checkpoint-20261011-03'
MODULE = 'TransferWordObjectPut01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-word-object-put-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 8 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 125 and len(pool['inherited_public_reports']) == 1063
manager_endpoint = DIAG / 'transfer-word-layer-flatten-endpoint-20261011-03'
manager_archive = manager_endpoint / 'portable-windows-word-layer-flatten-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == 'bce2913d5b200269c695776982274d49974db229d719ea6a410c35124a2215f6'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 4 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferWordLayerFlatten01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
assert len(combined_reports) == 1063 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 125
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
reference = {'word_layer_flatten': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 4},
    'ancestors': manager_reference, 'complete_owned_modules': 125, 'inherited_complete_reports': 1063,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact one-hundred-twenty-five-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging/keys/reader/authenticated snapshot/recovery/durable write closure, with 1063 original inherited complete reports; original recovery selected once without replay; shared StateDelta and seventeen Readback reports included once. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'source-derived canonical raw Scalar-word fields in concrete finite pending enum/list codec')
capstone = DIAG/'transfer-capstone-plan-20261011-01/plan.json'
assert pin(capstone) in plan['pins'] and pin(capstone)['sha256']=='d6ab4913d7b42c52b32357ac04bfc3da58b7b162140c2556bba90915d40ca067'
add(capstone, 'context/handwritten-capstone-plan.json', 'planning only: explicit native temporal/poison/snapshot/ICS23/library/Host/ownership/OS/full gate obligations; zero evidence credit')

add(stdout, 'reports/fresh-8-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete one-hundred-twenty-five-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 1063 inherited reports and exact source associations')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for attempt in [1,2]:
    failed=DIAG/('transfer-word-object-put-20261011-'+str(attempt).zfill(2))
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordObjectPut01.lean','project/ShielddSecurity/TransferWordObjectPut01.lean','context/checked-pending-put-shape.json']
    if attempt==1:names.append('runs/01-TransferWordObjectPut01/stdout.txt')
    for name in names:
        assert pin(failed/name) in plan['pins']
        add(failed/name,'unselected/'+str(attempt).zfill(2)+'/'+name,'original unsolved conditional equality01 or pre-Lean pressure02 retained; entire failed attempt zero proof/native/control credit including incomplete sorryAx output')
row=mapping['checked_pending_put_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'],'context/checked-pending-put-shape.json','exact source inner Any TypeId read and mismatch panic before boxed pending object insert; static association only')
row=mapping['saturating_capacity_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'],'context/saturating-capacity-shape.json','exact source pending length saturating_add comparison and consensus32768 literal; static association only')
row=mapping['checked_pending_read_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'],'context/checked-pending-read-shape.json','exact source getter downcast-before-Clone leaf/layer/parent branches and pending absence default; static association only')
row = mapping['r2_decoder_payload_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/r2-decoder-payload-shape.json', 'exact pinned R2 literal and decoder multiplication/CtOption static source association; native binding separate')
row = mapping['wide_reduction_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/wide-reduction-shape.json', 'exact four4MAC/upperADC groups with deferredcarry; static source only')
row = mapping['wide_product_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/wide-product-shape.json', 'exact16 MAC retained-row/carry static source association; primitive/compiler/final wide reduction binding separate')
row = mapping['scalar_decode_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/scalar-decoder-shape.json', 'four exact LE word reads/four SBB/low choice bit shape; static source only; R2 conversion separate')
row = mapping['corrected_finalization_source_order']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/corrected-finalization-call-order.json', 'fresh reordered inventory follows authenticated source call positions; static association only')
row = mapping['fixed_finalization_source_association']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/fixed-finalization-source-association.json', 'exact known returned SCT/compact finishing call-order association, not exhaustive native trace proof')
row = mapping['known_finalization_source_association']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/known-finalization-source-association.json', 'six exact source literals and known put/delete call shapes; static association, no exhaustive native trace proof')
row = mapping['action_projection_source_association']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/action-projection-source-association.json', 'exact input field/all-slot ordered iterator map/batch and Nullifier byte-forwarding shapes; static association only')
row = mapping['serializer_byte_source_association']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/serializer-byte-source-association.json', 'exact pinned array and four ordered LE byte slices; shape only, not native primitive or trace semantics')
row = mapping['serializer_wrapper_source_association']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/serializer-wrapper-source-association.json', 'exact constants/zero-high-limbs/four rounds/final subtraction structure, no semantic or native credit')

for row in mapping['word_primitive_context']:
    assert pin(row['path']) == row and row in plan['pins']
    add(row['path'], 'context/word-primitive-context/' + Path(row['path']).name, 'raw pinned registry source and authenticated cached crate association, not semantic proof')

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
review = {'status': 'FIXED_PENDING_TYPE_GUARDED_OBJECT_PUT_AND_CHECKED_READ_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 3, 'fresh_structure_audits': 0, 'fresh_theorem_audits': 5,
    'fresh_complete_public_audits': 8, 'fresh_audits': fresh, 'inherited_complete_public_audits': 1063,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 2, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained, three definitions/five theorems. Type-match Bool observes expected pending enum type, with same type for Open/Sealed. Absent/tombstoned or correct existing enum permits boxed put; previous wrong type panics before mutation. Successful modeled update derives exact latest write and other-key frame, then supported sealed codec derives checked read. Failed01 unsolved conditional equality and failed02 pre-Lean pressure retained as twenty-one complete raw files, all incomplete sorryAx reports zero credit. Fresh03 same repaired source as02 with direct conditional proof, unchanged limits/guards. Actual TypeId/inner Box/Any/Clone/map/locks/compiler/ownership and whole-program primitive correspondence remain explicit. Full Transfer OPEN; zero native/control/certification credit.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-word-object-put-endpoint-v1', 'entries': records,
    'fresh_audits': 8, 'inherited_audits': 1063, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 8, 'inherited_audits': 1063,
    'native_test_credit': 0, 'certification': False}))
