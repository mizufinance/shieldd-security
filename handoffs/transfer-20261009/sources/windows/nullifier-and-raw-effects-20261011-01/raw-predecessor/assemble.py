"""Seal the raw effect ordering and derived delivery discard proof with lossless provenance."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-raw-effects-source-20261011-03'
OLD = DIAG / 'transfer-raw-effects-source-20261011-02'
CHECKPOINT = DIAG / 'transfer-raw-effects-checkpoint-20261011-01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-raw-effects-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
rejected = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == len(rejected) == 2
assert events[-1]['result']['status'] == 'passed' and rejected[-1]['result']['status'] == 'failed'
spec = importlib.util.spec_from_file_location('complete_batch_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
stdout = CURRENT / 'runs/01-TransferRawEffectsSource01/stdout.txt'
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 27 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for record in events[-1]['result']['objects']:
    assert pin(record['path']) == record
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 4 and len(pool['inherited_public_reports']) == 57
for selected in pool['selected']:
    for key in ['source', 'object', 'copy']:
        assert pin(selected[key]['path']) == selected[key]
raw_root = DIAG / 'transfer-raw-state-endpoint-20261011-01'
vector_root = DIAG / 'transfer-reader-vector-endpoint-20261011-01'
raw_archive = raw_root / 'portable-windows-raw-state-endpoint01.tar.xz'
vector_archive = vector_root / 'portable-windows-reader-vector-endpoint01.tar.xz'
assert pin(raw_archive)['sha256'] == 'dec82e87d6d04c87765e34ee306a9de24636bb95834e886e8dca6cfc0b82c7f8'
assert pin(vector_archive)['sha256'] == 'b0e2c34ace35e4a23500d8bfc35a88d9429fe4852f66f0a73eecba2b567ff7ef'
batch_root = DIAG / 'transfer-nullifier-batch-endpoint-20261011-01'
batch_archive = batch_root / 'portable-windows-nullifier-batch-endpoint01.tar.xz'
assert pin(batch_archive)['sha256'] == 'd8bf71cf9d7be0fb87cdb1135e7b696638b43c7a38417598d027550d5f0b9411'
with tarfile.open(raw_archive, 'r:xz') as raw_tar, tarfile.open(vector_archive, 'r:xz') as vector_tar, tarfile.open(batch_archive, 'r:xz') as batch_tar:
    for selected in pool['selected']:
        tar = batch_tar if selected['module'] == 'TransferNullifierBatchSource01' else (vector_tar if selected['module'] == 'TransferNullifierReaderVector01' else raw_tar)
        assert tar.extractfile('source/ShielddSecurity/' + selected['module'] + '.lean').read() == Path(selected['source']['path']).read_bytes()
    raw_review = json.loads(raw_tar.extractfile('review.json').read())
    vector_review = json.loads(vector_tar.extractfile('review.json').read())
    batch_review = json.loads(batch_tar.extractfile('review.json').read())
    assert {**raw_review['fresh_audits'], **raw_review['inherited_audits'], **vector_review['fresh_audits'], **batch_review['fresh_audits']} == pool['inherited_public_reports']
queue_root = DIAG / 'transfer-deferred-queue-endpoint-20261010-01'
queue_archive = queue_root / 'portable-windows-deferred-queue-endpoint01.tar.xz'
assert pin(queue_archive)['sha256'] == 'eb830a8f56cd6927904dcf1564f4f53527863ab90dca0e8189f5c6c2ef250033'
with tarfile.open(queue_archive, 'r:xz') as tar:
    assert tar.extractfile('context/core-external-floor.json').read() == Path(plan['external_floor']['path']).read_bytes()
reference = {
    'raw': {'accepted_evidence_commit': 'ae307b2af3c98242cc6a3be82e5673d89b54f9c4', 'archive': pin(raw_archive), 'manifest': pin(raw_root / 'manifest.json')},
    'vector': {'accepted_evidence_commit': '2aae019bc518264d59e4d0ba590ada1d478c91f5', 'archive': pin(vector_archive), 'manifest': pin(vector_root / 'manifest.json')},
    'core_floor': {'accepted_evidence_commit': '7f4abf584595911545bd8a7645e487c629931cba', 'archive': pin(queue_archive), 'manifest': pin(queue_root / 'manifest.json'), 'archive_path': 'context/core-external-floor.json', 'original': plan['external_floor'], 'all_original_bytes_verified_equal': True},
    'batch': {'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'archive': pin(batch_archive), 'manifest': pin(batch_root / 'manifest.json')},
    'inherited_complete_declarations': 57, 'inherited_sources': 4,
    'all_inherited_source_and_report_identities_verified': True}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged guard provenance')
add(CURRENT / 'handwritten/TransferRawEffectsSource01.lean', 'source/ShielddSecurity/TransferRawEffectsSource01.lean', 'twelve definitions and fifteen finite reusable source-order/delivery proofs')
add(stdout, 'reports/fresh-27-complete-declarations.txt', 'all raw full declaration types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete exact four-module owned import root; object bytes omitted')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified accepted source/report/core-floor references')
for name in ['prepare.py', 'prepare_successor.py', 'plan.json', 'events.jsonl']:
    add(OLD / name, 'rejected/' + name, 'original rejected attempt; zero proof and negative-control credit')
add(OLD / 'handwritten/TransferRawEffectsSource01.lean', 'rejected/source.lean', 'original elaboration failures preserved unchanged')
add(OLD / 'runs/01-TransferRawEffectsSource01/stdout.txt', 'rejected/compiler-output.txt', 'complete original compiler rejection; never qualifying evidence')
prior = DIAG / 'transfer-raw-effects-source-20261011-01'
prior_plan = json.loads((prior / 'plan.json').read_bytes())
prior_events = [json.loads(s) for s in (prior / 'events.jsonl').read_text().splitlines()]
prior_stdout = prior / 'runs/01-TransferRawEffectsSource01/stdout.txt'
prior_audits = m.audit(prior_stdout.read_text(), prior_plan['targets'][0]['audit_names'])
assert prior_events[-1]['result']['status'] == 'passed' and len(prior_audits) == 23
assert prior_audits == prior_events[-1]['result']['audits'] and pin(prior_stdout) == prior_events[-1]['result']['stdout']
for name in ['prepare.py', 'plan.json', 'events.jsonl', 'review.json']:
    add(prior / name, 'prior-qualified/' + name, 'preserved original scoped 23-report version; not imported or added to current fresh census')
add(prior / 'handwritten/TransferRawEffectsSource01.lean', 'prior-qualified/source.lean', 'successful earlier callback-interface version; source snapshot unchanged')
add(prior_stdout, 'prior-qualified/complete-23-reports.txt', 'full original qualified declaration reports; not double-counted')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all 136 protected and foreign identities, main, lock and clean runtime preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for source in mapping['runtime_sources']:
    assert pin(source['path']) == source
    relative = Path(source['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(source['path'], 'runtime/' + relative, 'exact clean full-SHA runtime snapshot; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'full runtime SHA lock')
add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact fresh assembly derivation source')
add(Path(__file__), 'assemble.py', 'exact transport assembly source')
review = {
    'status': 'RAW_TRANSFER_CAPTURED_SOURCE_NOTE_EVENT_ORDER_LATE_VOLUME_RECHECK_AND_DELIVERY_DISCARD_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 12, 'fresh_theorem_audits': 15,
    'fresh_complete_public_audits': 27, 'fresh_audits': fresh,
    'inherited_complete_public_audits': 57, 'inherited_reference': reference,
    'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'runtime_sha': mapping['runtime_sha'], 'native_test_credit': 0, 'negative_control_credit': 0,
    'rejected_attempts': 1, 'rejected_proof_credit': 0, 'certification': False, 'full_transfer': 'OPEN',
    'interfaces': mapping['interfaces'], 'prior_qualified_reports': prior_audits, 'prior_qualified_fresh_census_credit': 0,
    'scope': mapping['scope'] + ' Capability mismatch precedes effects. Missing reshape source is checked even for empty inputs. Captured source-id observation is passed to all note callbacks; ordinary volume source is reacquired after note effects. A successful nullifier callback dispatches an exhaustive ordered spend-event loop before any note callback. Note failure retains its failing cache, omits that semantic note-created event and stops the suffix; internal SCT events and partial mutations remain callback behavior. Volume recheck success derives the exact two verifiable [1] writes and their frame, with explicit entry/day key separation. The actual late spent observation after successful reshape derives a raw error retaining earlier child effects, suppression of volume payload insertion, and enclosing delivery rejection with original parent/queue retained. Successful reshape remains an explicit observed upstream interface, not an unconditional runtime theorem. SCT/Merkle, codecs, collection/ownership and durability correspondence remain open. Preserved qualified 01 is not double-counted; failed 02 is zero credit.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete fresh audits, retained rejection, conclusions and interfaces')
manifest = {'schema': 'transfer-raw-effects-endpoint-v1', 'entries': records,
    'fresh_audits': 27, 'inherited_audits': 57, 'inherited_reference': reference,
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
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'), 'review': pin(ROOT / 'review.json'), 'entries': len(records), 'members': len(payload), 'fresh_audits': 27, 'inherited_audits': 57, 'native_test_credit': 0, 'certification': False}))
