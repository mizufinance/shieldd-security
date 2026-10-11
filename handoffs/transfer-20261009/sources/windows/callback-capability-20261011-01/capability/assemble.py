"""Seal exact complete-item capability comparison and upstream interfaces."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-capability-source-20261011-02'
REJECTED = DIAG / 'transfer-capability-source-20261011-01'
CHECKPOINT = DIAG / 'transfer-capability-checkpoint-20261011-01'
MODULE = 'TransferCapabilitySource01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-capability-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('capability_complete_auditor', CURRENT / 'execute_bounded.py')
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
rejected = [json.loads(s) for s in (REJECTED / 'events.jsonl').read_text().splitlines()]
assert len(rejected) == 2 and rejected[-1]['result']['status'] == 'failed'
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 5 and len(pool['inherited_public_reports']) == 84
manager_endpoint = DIAG / 'transfer-note-manager-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-note-manager-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == '669cb795b7221dbcffd6ecf0c6eaf663f6fe71eca86cba8a4f8708dd38ccfc1f'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    ancestor_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
assert manager_pool['inherited_public_reports'] == pool['inherited_public_reports']
assert {r['module'] for r in pool['selected']} == {r['module'] for r in manager_pool['selected']}
for selected in pool['selected']:
    original = next(r for r in manager_pool['selected'] if r['module'] == selected['module'])
    assert selected['source'] == original['source'] and selected['object'] == original['object']
    for k in ['source', 'object', 'copy']:
        assert pin(selected[k]['path']) == selected[k]
    tag = {'TransferStateDelta': 'raw', 'TransferRawStateProgram01': 'raw',
        'TransferNullifierReaderVector01': 'vector', 'TransferNullifierBatchSource01': 'batch', 'TransferRawEffectsSource01': 'effects'}[selected['module']]
    carrier = ancestor_reference[tag]['archive']
    assert pin(carrier['path']) == carrier
    with tarfile.open(carrier['path'], 'r:xz') as tar:
        assert tar.extractfile('source/ShielddSecurity/' + selected['module'] + '.lean').read() == Path(selected['source']['path']).read_bytes()
assert ancestor_reference['core_floor']['original'] == plan['external_floor']
reference = {'shared_closure_reference_carrier': {'archive': pin(manager_archive),
    'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE',
    'manager_module_imported': False, 'manager_13_reports_added_to_current_census': False},
    'ancestors': ancestor_reference, 'complete_owned_modules': 5, 'inherited_complete_reports': 84,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Shared five-module raw closure only. NoteManager current module and its 13 reports are separate context, not an import or fresh replay in this capability module.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guard provenance')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'six definitions and five exact comparison/source proofs')
add(stdout, 'reports/fresh-11-complete-declarations.txt', 'all raw full declaration types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete five-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified exact 84-report source closure associations')
for name in ['prepare.py', 'prepare_recipe.py', 'plan.json', 'events.jsonl']:
    add(REJECTED / name, 'rejected/' + name, 'preserved original warning-rejected attempt; zero credit')
add(REJECTED / ('handwritten/' + MODULE + '.lean'), 'rejected/source.lean', 'original strict style warning proof source')
add(REJECTED / ('runs/01-' + MODULE + '/stdout.txt'), 'rejected/compiler-output.txt', 'full original reports including warning; compiler exit zero does not qualify')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
    relative = Path(row['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(row['path'], 'runtime/' + relative, 'exact clean pinned runtime source; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'EXACT_COMPLETE_ITEM_CAPABILITY_REEXTRACTION_COMPARISON_AND_BOUND_LATE_CONFLICT_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 6, 'fresh_theorem_audits': 5,
    'fresh_complete_public_audits': 11, 'fresh_audits': fresh, 'inherited_complete_public_audits': 84,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 1, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' Whole wrapper execution success derives successful extraction of exactly the token item in its context through the executable equality check; no desired exactMatched boolean is a premise. Extraction failure and unequal complete item retain the input cache and precede all raw effects. Exact successful rebinding dispatches projections of the same captured action with Ordinary/FeeFunding from the token context. Actual verified-token provenance, extractor internals, real Verification equality/bytes and Item-to-effect semantic projection remain interfaces. Bound Ordinary current volume conflict derives the raw error retaining the earlier cache. The first compiler-zero warning output is rejected as a whole and adds no proof or negative-control credit.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current census, original rejection and exact binding interfaces')
manifest = {'schema': 'transfer-capability-endpoint-v1', 'entries': records,
    'fresh_audits': 11, 'inherited_audits': 84, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 11, 'inherited_audits': 84,
    'native_test_credit': 0, 'certification': False}))
