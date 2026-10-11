"""Seal the source-ordered nullifier batch proof with lossless provenance."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-nullifier-batch-source-20261011-02'
OLD = DIAG / 'transfer-nullifier-batch-source-20261011-01'
CHECKPOINT = DIAG / 'transfer-nullifier-batch-checkpoint-20261011-01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-nullifier-batch-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
rejected = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == len(rejected) == 2
assert events[-1]['result']['status'] == 'passed' and rejected[-1]['result']['status'] == 'failed'
spec = importlib.util.spec_from_file_location('complete_batch_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
stdout = CURRENT / 'runs/01-TransferNullifierBatchSource01/stdout.txt'
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 16 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for record in events[-1]['result']['objects']:
    assert pin(record['path']) == record
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 3 and len(pool['inherited_public_reports']) == 41
for selected in pool['selected']:
    for key in ['source', 'object', 'copy']:
        assert pin(selected[key]['path']) == selected[key]
raw_root = DIAG / 'transfer-raw-state-endpoint-20261011-01'
vector_root = DIAG / 'transfer-reader-vector-endpoint-20261011-01'
raw_archive = raw_root / 'portable-windows-raw-state-endpoint01.tar.xz'
vector_archive = vector_root / 'portable-windows-reader-vector-endpoint01.tar.xz'
assert pin(raw_archive)['sha256'] == 'dec82e87d6d04c87765e34ee306a9de24636bb95834e886e8dca6cfc0b82c7f8'
assert pin(vector_archive)['sha256'] == 'b0e2c34ace35e4a23500d8bfc35a88d9429fe4852f66f0a73eecba2b567ff7ef'
with tarfile.open(raw_archive, 'r:xz') as raw_tar, tarfile.open(vector_archive, 'r:xz') as vector_tar:
    for selected in pool['selected']:
        tar = vector_tar if selected['module'] == 'TransferNullifierReaderVector01' else raw_tar
        assert tar.extractfile('source/ShielddSecurity/' + selected['module'] + '.lean').read() == Path(selected['source']['path']).read_bytes()
    raw_review = json.loads(raw_tar.extractfile('review.json').read())
    vector_review = json.loads(vector_tar.extractfile('review.json').read())
    assert {**raw_review['fresh_audits'], **raw_review['inherited_audits'], **vector_review['fresh_audits']} == pool['inherited_public_reports']
queue_root = DIAG / 'transfer-deferred-queue-endpoint-20261010-01'
queue_archive = queue_root / 'portable-windows-deferred-queue-endpoint01.tar.xz'
assert pin(queue_archive)['sha256'] == 'eb830a8f56cd6927904dcf1564f4f53527863ab90dca0e8189f5c6c2ef250033'
with tarfile.open(queue_archive, 'r:xz') as tar:
    assert tar.extractfile('context/core-external-floor.json').read() == Path(plan['external_floor']['path']).read_bytes()
reference = {
    'raw': {'accepted_evidence_commit': 'ae307b2af3c98242cc6a3be82e5673d89b54f9c4', 'archive': pin(raw_archive), 'manifest': pin(raw_root / 'manifest.json')},
    'vector': {'accepted_evidence_commit': '2aae019bc518264d59e4d0ba590ada1d478c91f5', 'archive': pin(vector_archive), 'manifest': pin(vector_root / 'manifest.json')},
    'core_floor': {'accepted_evidence_commit': '7f4abf584595911545bd8a7645e487c629931cba', 'archive': pin(queue_archive), 'manifest': pin(queue_root / 'manifest.json'), 'archive_path': 'context/core-external-floor.json', 'original': plan['external_floor'], 'all_original_bytes_verified_equal': True},
    'inherited_complete_declarations': 41, 'inherited_sources': 3,
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
add(CURRENT / 'handwritten/TransferNullifierBatchSource01.lean', 'source/ShielddSecurity/TransferNullifierBatchSource01.lean', 'seven definitions and nine finite reusable batch source proofs')
add(stdout, 'reports/fresh-16-complete-declarations.txt', 'all raw full declaration types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete exact three-module owned import root; object bytes omitted')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified accepted source/report/core-floor references')
for name in ['prepare.py', 'plan.json', 'events.jsonl']:
    add(OLD / name, 'rejected/' + name, 'original rejected attempt; zero proof and negative-control credit')
add(OLD / 'handwritten/TransferNullifierBatchSource01.lean', 'rejected/source.lean', 'original elaboration failures preserved unchanged')
add(OLD / 'runs/01-TransferNullifierBatchSource01/stdout.txt', 'rejected/compiler-output.txt', 'complete original compiler rejection; never qualifying evidence')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all 136 protected and foreign identities, main, lock and clean runtime preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for source in mapping['runtime_sources']:
    assert pin(source['path']) == source
    relative = Path(source['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(source['path'], 'runtime/' + relative, 'exact clean full-SHA runtime snapshot; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'full runtime SHA lock')
add(Path(__file__), 'assemble.py', 'exact transport assembly source')
review = {
    'status': 'PUBLIC_NULLIFIER_BATCH_SOURCE_ORDER_CAPACITY_ALL_INPUT_FRESHNESS_AND_SINGLE_OBJECT_WRITE_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 7, 'fresh_theorem_audits': 9,
    'fresh_complete_public_audits': 16, 'fresh_audits': fresh,
    'inherited_complete_public_audits': 41, 'inherited_reference': reference,
    'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'runtime_sha': mapping['runtime_sha'], 'native_test_credit': 0, 'negative_control_credit': 0,
    'rejected_attempts': 1, 'rejected_proof_credit': 0, 'certification': False, 'full_transfer': 'OPEN',
    'interfaces': mapping['interfaces'], 'capacity': mapping['capacity'], 'cache': mapping['cache'], 'order': mapping['order'],
    'scope': mapping['scope'] + ' Successful actual modeled inspection derives the source-ordered checks, capacity bound, ordered append, and observed unspent flags/current pending freshness for every input using the qualified complete vector recurrence. Nonempty public success derives exactly one pending-object cache write and frames verifiable/NV/events and all other object keys. Errors preserve the supplied input cache, including possible earlier raw effects; this is not whole-handler rollback. Saturating capacity implies natural sum capacity only with explicit capacity<wordMax. Pending getter/encoding, source-id, word size, nullifier equality, Rust collections/cache ownership and individually authenticated status remain named interfaces. Original elaboration failure is zero credit.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete fresh audits, retained rejection, conclusions and interfaces')
manifest = {'schema': 'transfer-nullifier-batch-endpoint-v1', 'entries': records,
    'fresh_audits': 16, 'inherited_audits': 41, 'inherited_reference': reference,
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
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'), 'review': pin(ROOT / 'review.json'), 'entries': len(records), 'members': len(payload), 'fresh_audits': 16, 'inherited_audits': 41, 'native_test_credit': 0, 'certification': False}))
