"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-scalar-padded-carry-20261011-03'
CHECKPOINT = DIAG / 'transfer-scalar-padded-carry-checkpoint-20261011-03'
MODULE = 'TransferScalarPaddedCarry01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-scalar-padded-carry-endpoint01.tar.xz'
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
assert pool['objects'] == 89 and len(pool['inherited_public_reports']) == 842
manager_endpoint = DIAG / 'transfer-typed-scalar-publication-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-typed-scalar-publication-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == 'ac74e64e72236e0afa9700349fbfba007c3a8d7b6b8e68663eed51f3659fce57'
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
manager_selected = manager_pool['selected'] + [{'module': 'TransferTypedScalarPublication01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
assert len(combined_reports) == 842 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 89
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
reference = {'typed_scalar_publication': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 3},
    'ancestors': manager_reference, 'complete_owned_modules': 89, 'inherited_complete_reports': 842,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact eighty-nine-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging/keys/reader/authenticated snapshot/recovery/durable write closure, with 842 original inherited complete reports; original recovery selected once without replay; shared StateDelta and seventeen Readback reports included once. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'explicit padded MAC/ADC source schedule derives all zero ignored carries, exact 32-byte canonical Montgomery serializer')
capstone = DIAG/'transfer-capstone-plan-20261011-01/plan.json'
assert pin(capstone) in plan['pins'] and pin(capstone)['sha256']=='d6ab4913d7b42c52b32357ac04bfc3da58b7b162140c2556bba90915d40ca067'
add(capstone, 'context/handwritten-capstone-plan.json', 'planning only: explicit native temporal/poison/snapshot/ICS23/library/Host/ownership/OS/full gate obligations; zero evidence credit')

add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact maintained proof-only let reduction source, guards unchanged')
failed01=DIAG/'transfer-scalar-padded-carry-20261011-01'
failedEvents=[json.loads(x) for x in (failed01/'events.jsonl').read_text().splitlines()]
assert failedEvents[-1]['result']['status']=='failed' and failedEvents[-1]['result']['reason']=='Physical memory pressure'
assert not (failed01/'runs/01-TransferScalarPaddedCarry01/stdout.txt').exists()
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarPaddedCarry01.lean','project/ShielddSecurity/TransferScalarPaddedCarry01.lean']:
    assert pin(failed01/n) in plan['pins']
    add(failed01/n,'rejected/01/'+n,'owned physical-memory monitor stop before stdout was saved; no proof/control credit')
failed02=DIAG/'transfer-scalar-padded-carry-20261011-02'
assert (failed01/'handwritten/TransferScalarPaddedCarry01.lean').read_bytes()==(failed02/'handwritten/TransferScalarPaddedCarry01.lean').read_bytes()
for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarPaddedCarry01.lean','project/ShielddSecurity/TransferScalarPaddedCarry01.lean','runs/01-TransferScalarPaddedCarry01/stdout.txt']:
    assert pin(failed02/n) in plan['pins']
    add(failed02/n,'rejected/02/'+n,'identical fresh attempt reached Lean; local bindings prevented exact ADC rewrite; raw reports/error retained, zero credit')
add(stdout, 'reports/fresh-6-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete eighty-nine-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 842 inherited reports and exact source associations')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
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
review = {'status': 'SOURCE_SCALAR_EXPLICIT_PADDED_MAC_ADC_CARRY_SCHEDULE_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 3, 'fresh_theorem_audits': 3,
    'fresh_complete_public_audits': 6, 'fresh_audits': fresh, 'inherited_complete_public_audits': 842,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 2, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' Six complete full type/axiom reports retained. Failed01 memory-pressure stop preserved with no saved stdout, failed02 identical source/full raw rewrite error preserved; both zero credit. Fresh03 proof-only local binding reduction leaves six contracts unchanged. Explicit source padding recurrence derives every ignored carry zero and exact serializer, retaining Rust primitive/native trace/compiler/type/library correspondence obligations. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-scalar-padded-carry-endpoint-v1', 'entries': records,
    'fresh_audits': 6, 'inherited_audits': 842, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 6, 'inherited_audits': 842,
    'native_test_credit': 0, 'certification': False}))
