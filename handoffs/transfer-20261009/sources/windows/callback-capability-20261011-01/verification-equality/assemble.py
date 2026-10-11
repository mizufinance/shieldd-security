"""Seal compared-field equality with complete decider audit and exact closure."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-verification-equality-source-20261011-02'
REJECTED = DIAG / 'transfer-verification-equality-source-20261011-01'
CHECKPOINT = DIAG / 'transfer-verification-equality-checkpoint-20261011-01'
MODULE = 'TransferVerificationEqualitySource01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-verification-equality-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('fieldwise_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 13 and fresh == events[-1]['result']['audits']
assert MODULE in plan['targets'][0]['source']['path']
assert 'ShielddSecurity.' + MODULE + '.instDecidableEqItem' in fresh
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
rejected = [json.loads(s) for s in (REJECTED / 'events.jsonl').read_text().splitlines()]
assert len(rejected) == 2 and rejected[-1]['result']['status'] == 'failed'
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 6 and len(pool['inherited_public_reports']) == 95
cap_endpoint = DIAG / 'transfer-capability-endpoint-20261011-01'
cap_archive = cap_endpoint / 'portable-windows-capability-endpoint01.tar.xz'
assert pin(cap_archive)['sha256'] == '7917b5b6918bbf436bf77e1aca97b7e0159e9f724ef0941eac324f25044c1334'
with tarfile.open(cap_archive, 'r:xz') as tar:
    cap_review = json.loads(tar.extractfile('review.json').read())
    cap_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    cap_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    cap_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    cap_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    cap_stdout = tar.extractfile('reports/fresh-11-complete-declarations.txt').read().decode()
    cap_reports = m.audit(cap_stdout, cap_plan['targets'][0]['audit_names'])
assert len(cap_reports) == 11 and cap_reports == cap_review['fresh_audits'] == cap_events[-1]['result']['audits']
assert {**cap_pool['inherited_public_reports'], **cap_reports} == pool['inherited_public_reports']
cap_selected = cap_pool['selected'] + [{'module': 'TransferCapabilitySource01',
    'source': cap_plan['targets'][0]['source'], 'object': cap_events[-1]['result']['objects'][0]}]
for selected in pool['selected']:
    original = next(r for r in cap_selected if r['module'] == selected['module'])
    assert selected['source'] == original['source'] and selected['object'] == original['object']
    for k in ['source', 'object', 'copy']:
        assert pin(selected[k]['path']) == selected[k]
    if selected['module'] == 'TransferCapabilitySource01':
        carrier = pin(cap_archive)
    else:
        tag = {'TransferStateDelta': 'raw', 'TransferRawStateProgram01': 'raw',
            'TransferNullifierReaderVector01': 'vector', 'TransferNullifierBatchSource01': 'batch', 'TransferRawEffectsSource01': 'effects'}[selected['module']]
        carrier = cap_reference['ancestors'][tag]['archive']
    assert pin(carrier['path']) == carrier
    with tarfile.open(carrier['path'], 'r:xz') as tar:
        assert tar.extractfile('source/ShielddSecurity/' + selected['module'] + '.lean').read() == Path(selected['source']['path']).read_bytes()
assert cap_reference['ancestors']['core_floor']['original'] == plan['external_floor']
reference = {'capability': {'archive': pin(cap_archive), 'manifest': pin(cap_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 11},
    'ancestors': cap_reference, 'complete_owned_modules': 6, 'inherited_complete_reports': 95,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Six exact owned modules, including actual capability module; NoteManager is a separate reference carrier, not an import in this closure.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'four compared-field definitions, eight theorems and derived decider')
add(stdout, 'reports/fresh-13-complete-declarations.txt', 'all full raw types and standard axioms including generated DecidableEq instance')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete six-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'exact 95 inherited report and source associations')
for name in ['prepare.py', 'prepare_recipe.py', 'plan.json', 'events.jsonl']:
    add(REJECTED / name, 'rejected/' + name, 'preserved conjunction-association rejection; zero credit')
add(REJECTED / ('handwritten/' + MODULE + '.lean'), 'rejected/source.lean', 'exact original failed source')
add(REJECTED / ('runs/01-' + MODULE + '/stdout.txt'), 'rejected/compiler-output.txt', 'full original failed compiler output; no proof or negative-control credit')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
    relative = Path(row['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(row['path'], 'runtime/' + relative, 'exact pinned PartialEq/ensure_binds runtime source; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'VERIFICATION_FAMILY_SCALAR_ENVELOPE_COMPARISON_AND_VERIFIED_ITEM_BINDING_QUALIFIED',
    'fresh_sources': 1, 'fresh_explicit_definition_audits': 4, 'fresh_derived_instance_audits': 1, 'fresh_theorem_audits': 8,
    'fresh_complete_public_audits': 13, 'fresh_audits': fresh, 'inherited_complete_public_audits': 95,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 1, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' The public instance generated by deriving DecidableEq is explicitly audited. Operational conjunction equality is equivalent to equality of the three represented fields; this instantiates generic item comparison in the capability wrapper. ensure_binds success recovers requested family and all compared fields; registry independence is explicitly proved because that method does not inspect registry_id. Scalar/envelope equality does not establish proof validity, source statement preimage equality, cryptographic hash injectivity, registry provenance or semantic correspondence. Field-mismatch refusals are logical model conclusions only.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete instance/type/axiom census and exact identity versus semantics scope')
manifest = {'schema': 'transfer-verification-equality-endpoint-v1', 'entries': records,
    'fresh_audits': 13, 'inherited_audits': 95, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 13, 'inherited_audits': 95,
    'native_test_credit': 0, 'certification': False}))
