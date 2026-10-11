"""Seal exact NoteManager callback composition and scoped inherited receipts."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-note-manager-source-20261011-03'
PRIOR = DIAG / 'transfer-note-manager-source-20261011-02'
REJECTED = DIAG / 'transfer-note-manager-source-20261011-01'
CHECKPOINT = DIAG / 'transfer-note-manager-checkpoint-20261011-01'
MODULE = 'TransferNoteManagerSource01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-note-manager-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('manager_complete_auditor', CURRENT / 'execute_bounded.py')
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
prior_plan = json.loads((PRIOR / 'plan.json').read_bytes())
prior_events = [json.loads(s) for s in (PRIOR / 'events.jsonl').read_text().splitlines()]
prior_stdout = PRIOR / ('runs/01-' + MODULE + '/stdout.txt')
assert prior_events[-1]['result']['status'] == 'passed'
prior_audits = m.audit(prior_stdout.read_text(), prior_plan['targets'][0]['audit_names'])
assert prior_audits == fresh == prior_events[-1]['result']['audits']
assert pin(prior_stdout) == prior_events[-1]['result']['stdout']
assert Path(plan['targets'][0]['source']['path']).read_bytes() == Path(prior_plan['targets'][0]['source']['path']).read_bytes()
rejected_events = [json.loads(s) for s in (REJECTED / 'events.jsonl').read_text().splitlines()]
assert len(rejected_events) == 2 and rejected_events[-1]['result']['status'] == 'failed'
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 5 and len(pool['inherited_public_reports']) == 84
ancestors = [
    ('raw', 'transfer-raw-state-endpoint-20261011-01', 'portable-windows-raw-state-endpoint01.tar.xz', 'dec82e87d6d04c87765e34ee306a9de24636bb95834e886e8dca6cfc0b82c7f8'),
    ('vector', 'transfer-reader-vector-endpoint-20261011-01', 'portable-windows-reader-vector-endpoint01.tar.xz', 'b0e2c34ace35e4a23500d8bfc35a88d9429fe4852f66f0a73eecba2b567ff7ef'),
    ('batch', 'transfer-nullifier-batch-endpoint-20261011-01', 'portable-windows-nullifier-batch-endpoint01.tar.xz', 'd8bf71cf9d7be0fb87cdb1135e7b696638b43c7a38417598d027550d5f0b9411'),
    ('effects', 'transfer-raw-effects-context-endpoint-20261011-01', 'portable-windows-raw-effects-context-endpoint01.tar.xz', '769c7936e6b9ba20b6189f24f0c76c16c1c433887357992d8627f2c62dbd45fa')]
reference = {}
inherited = {}
module_owners = {'TransferStateDelta': 'raw', 'TransferRawStateProgram01': 'raw',
    'TransferNullifierReaderVector01': 'vector', 'TransferNullifierBatchSource01': 'batch', 'TransferRawEffectsSource01': 'effects'}
for tag, folder, filename, sha in ancestors:
    endpoint = DIAG / folder
    path = endpoint / filename
    assert pin(path)['sha256'] == sha
    with tarfile.open(path, 'r:xz') as tar:
        review = json.loads(tar.extractfile('review.json').read())
        inherited.update(review['fresh_audits'])
        if tag == 'raw':
            inherited.update(review['inherited_audits'])
        for selected in pool['selected']:
            if module_owners[selected['module']] == tag:
                assert tar.extractfile('source/ShielddSecurity/' + selected['module'] + '.lean').read() == Path(selected['source']['path']).read_bytes()
    reference[tag] = {'archive': pin(path), 'manifest': pin(endpoint / 'manifest.json'),
        'status': {'raw': 'PARENT_ACCEPTED_AND_PUBLISHED', 'vector': 'PARENT_ACCEPTED_AND_PUBLISHED',
            'batch': 'PARENT_REVIEW_ACCEPTED; PUBLICATION_SEPARATE', 'effects': 'CORRECTED_SUCCESSOR_LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_REVIEW_SEPARATE'}[tag]}
assert inherited == pool['inherited_public_reports']
for selected in pool['selected']:
    for k in ['source', 'object', 'copy']:
        assert pin(selected[k]['path']) == selected[k]
context_review = json.loads((DIAG / 'transfer-raw-effects-context-endpoint-20261011-01/review.json').read_bytes())
reference['core_floor'] = context_review['prior_reference']['core_floor_original_reference']
assert reference['core_floor']['original'] == plan['external_floor']
reference.update({'complete_owned_modules': 5, 'inherited_complete_reports': 84,
    'all_inherited_source_and_report_identities_verified': True,
    'prior_manager_source_and_13_reports_identical': True, 'prior_manager_new_credit': 0})
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged guard provenance')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'five definitions and eight callback/source proofs')
add(stdout, 'reports/fresh-13-complete-declarations.txt', 'all full raw types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'exact five-module import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'lossless 84-report and source associations')
for folder, tag, filenames in [(REJECTED, 'rejected', ['prepare.py', 'plan.json', 'events.jsonl']),
    (PRIOR, 'prior-qualified', ['prepare.py', 'prepare_successor.py', 'plan.json', 'events.jsonl'])]:
    for name in filenames:
        add(folder / name, tag + '/' + name, 'preserved original provenance; no additional fresh credit')
    add(folder / ('handwritten/' + MODULE + '.lean'), tag + '/source.lean', 'exact original source snapshot')
    add(folder / ('runs/01-' + MODULE + '/stdout.txt'), tag + '/compiler-output.txt', 'full original compiler reports; rejected attempt zero credit')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
    relative = Path(row['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(row['path'], 'runtime/' + relative, 'exact pinned runtime source snapshot; correspondence interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'SCT_POSITION_PENDING_PAYLOAD_APPEND_AND_RAW_NOTE_VOLUME_CALLBACK_COMPOSITION_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 5, 'fresh_theorem_audits': 8,
    'fresh_complete_public_audits': 13, 'fresh_audits': fresh, 'inherited_complete_public_audits': 84,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 1, 'rejected_proof_credit': 0,
    'prior_qualified_reports': 13, 'prior_qualified_new_credit': 0,
    'pre_admission_cli_refusal_credit': 0,
    'pre_admission_cli_refusal': 'An INVALID placeholder plan hash was refused before any Lean attempt; current03 ran once only with exact reviewed SHA.',
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' Success derives the actual SCT return position, current post-SCT pending getter, exact append tuple and one pending object update. Additional update frames post-SCT verifiable/NV/events/other objects, not original input cache. Note callback SCT failure retains its actual failure cache and suppresses semantic note-created and all later outputs; successful note preserves internal SCT events then appends one semantic event. Ordinary payload failure occurs after two marker writes and retains its actual failed SCT cache; those earlier markers are not asserted to survive an arbitrary callback overwrite. All underlying SCT/codec/ownership/alias/durability interfaces remain explicit.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current census and precise callback/error scope')
manifest = {'schema': 'transfer-note-manager-endpoint-v1', 'entries': records,
    'fresh_audits': 13, 'inherited_audits': 84, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 13, 'inherited_audits': 84,
    'native_test_credit': 0, 'certification': False}))
