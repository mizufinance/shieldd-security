"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-canonical-word-equality-20261011-02'
CHECKPOINT = DIAG / 'transfer-canonical-word-equality-checkpoint-20261011-02'
MODULE = 'TransferCanonicalWordEquality01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-canonical-word-equality-endpoint01.tar.xz'
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
assert pool['objects'] == 101 and len(pool['inherited_public_reports']) == 911
manager_endpoint = DIAG / 'transfer-complete-block-driver-endpoint-20261011-02'
manager_archive = manager_endpoint / 'portable-windows-complete-block-driver-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == '351f336d80a662de1e1abbbe37f0584d2cad5bc54f3d3e379c753c2915bacc22'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-2-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 2 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferCompleteBlockDriver01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
assert len(combined_reports) == 911 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 101
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
reference = {'complete_block_driver': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 2},
    'ancestors': manager_reference, 'complete_owned_modules': 101, 'inherited_complete_reports': 911,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact one-hundred-one-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging/keys/reader/authenticated snapshot/recovery/durable write closure, with 911 original inherited complete reports; original recovery selected once without replay; shared StateDelta and seventeen Readback reports included once. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'canonical internal raw word equality iff mathematical Montgomery value equality iff source serialized byte equality')
capstone = DIAG/'transfer-capstone-plan-20261011-01/plan.json'
assert pin(capstone) in plan['pins'] and pin(capstone)['sha256']=='d6ab4913d7b42c52b32357ac04bfc3da58b7b162140c2556bba90915d40ca067'
add(capstone, 'context/handwritten-capstone-plan.json', 'planning only: explicit native temporal/poison/snapshot/ICS23/library/Host/ownership/OS/full gate obligations; zero evidence credit')

add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact explicit beta-expression proof repair; finite guards unchanged')
failed=DIAG/'transfer-canonical-word-equality-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalWordEquality01.lean','project/ShielddSecurity/TransferCanonicalWordEquality01.lean','runs/01-TransferCanonicalWordEquality01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected-kernel/01/'+n,'beta-expression rewrite compiler failure; zero proof/control credit')
old=(failed/'handwritten/TransferCanonicalWordEquality01.lean').read_text()
a='      rw [packed_word_cons_division_recovers_exact_tail, packed_word_cons_division_recovers_exact_tail] at tails'
old=old.replace(a,'      change packWords (head :: rest) / radix64 = packWords (other :: tail) / radix64 at tails\n'+a)
a='    rw [leftRelation, rightRelation, Nat.mod_eq_of_lt left.canonical, Nat.mod_eq_of_lt right.canonical] at packed'
old=old.replace(a,'    change (radix64 ^ 4 * montgomeryValue left.words) % nullifierModulus = (radix64 ^ 4 * montgomeryValue right.words) % nullifierModulus at packed\n'+a)
assert old==(CURRENT/'handwritten/TransferCanonicalWordEquality01.lean').read_text()
add(stdout, 'reports/fresh-6-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete one-hundred-one-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 911 inherited reports and exact source associations')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
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
review = {'status': 'SOURCE_CANONICAL_INTERNAL_WORD_MATH_BYTE_EQUALITY_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 0, 'fresh_structure_audits': 1, 'fresh_theorem_audits': 5,
    'fresh_complete_public_audits': 6, 'fresh_audits': fresh, 'inherited_complete_public_audits': 911,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 1, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' Six complete full type/axiom reports retained. Failed01 rewrite output retained raw and unselected, zero credit. Fresh02 two explicit beta-expression proof steps leave six contracts unchanged. Canonical domain packWords less than p is explicit; no arbitrary raw-word serializer injectivity claim. Inherited FixedFinalizer list remains its defined model; native source-order correspondence OPEN pending fresh correction. Driver parent manifest has inherited rejected_attempts zero field despite its one raw preserved failed witness; actual count is one and zero credit. Native private Scalar invariant/PartialEq/constant-time primitive/word selector/bytes/hash/Clone/collection/full trace/cache/snapshot/ownership/OS bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-canonical-word-equality-endpoint-v1', 'entries': records,
    'fresh_audits': 6, 'inherited_audits': 911, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 6, 'inherited_audits': 911,
    'native_test_credit': 0, 'certification': False}))
