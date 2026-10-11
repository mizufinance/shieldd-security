"""Seal map/collect alignment, in-place pending zip and exhaustive unspent checks."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-nullifier-reader-vector-20261011-03'
CHECKPOINT = DIAG / 'transfer-reader-vector-checkpoint-20261011-01'
QUEUE = DIAG / 'transfer-deferred-queue-endpoint-20261010-01'
READBACK = DIAG / 'transfer-readback-recovery-publication-20261010-02'
READBACK_ENDPOINT = DIAG / 'transfer-readback-publication-endpoint-20261010-01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

archive = ROOT / 'portable-windows-reader-vector-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
spec = importlib.util.spec_from_file_location('reader_vector_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
stdout = CURRENT / 'runs/01-TransferNullifierReaderVector01/stdout.txt'
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 13 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for record in events[-1]['result']['objects']:
    assert pin(record['path']) == record
assert not plan['owned_imports']
empty = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert empty['objects'] == 0 and not empty['selected']
queue_archive = QUEUE / 'portable-windows-deferred-queue-endpoint01.tar.xz'
assert pin(queue_archive)['sha256'] == 'eb830a8f56cd6927904dcf1564f4f53527863ab90dca0e8189f5c6c2ef250033'
with tarfile.open(queue_archive, 'r:xz') as tar:
    assert tar.extractfile('context/core-external-floor.json').read() == Path(plan['external_floor']['path']).read_bytes()
readback_archive = READBACK_ENDPOINT / 'portable-windows-readback-publication-endpoint01.tar.xz'
assert pin(readback_archive)['sha256'] == '48b33b403223914e40cfedfd0d6031e68bde14fa5b659a72823caed344de47a8'
readback_plan = json.loads((READBACK / 'plan.json').read_bytes())
readback_target = next(t for t in readback_plan['targets'] if t['module'] == 'TransferReadback')
readback_stdout = READBACK / 'runs/01-TransferReadback/stdout.txt'
with tarfile.open(readback_archive, 'r:xz') as tar:
    assert tar.extractfile('source/ShielddSecurity/TransferReadback.lean').read() == Path(readback_target['source']['path']).read_bytes()
    assert tar.extractfile('reports/TransferReadback-complete-types-and-axioms.txt').read() == readback_stdout.read_bytes()
    assert tar.extractfile('context/empty-owned-composition-review.json').read() == Path(plan['owned_import_pool']['path']).read_bytes()
upstream = m.audit(readback_stdout.read_text(), readback_target['audit_names'])
assert len(upstream) == 17
reference = {'core_floor': {'accepted_archive': pin(queue_archive), 'accepted_manifest': pin(QUEUE / 'manifest.json'),
    'accepted_evidence_commit': '7f4abf584595911545bd8a7645e487c629931cba',
    'archive_path': 'context/core-external-floor.json', 'original': plan['external_floor'], 'all_original_bytes_verified_equal': True},
    'upstream_status_authentication': {'accepted_archive': pin(readback_archive),
        'accepted_manifest': pin(READBACK_ENDPOINT / 'manifest.json'),
        'accepted_evidence_commit': '35998917369a3d6479771403bba3f206a1a8ebb3',
        'source': readback_target['source'], 'stdout': pin(readback_stdout), 'complete_reports': upstream,
        'scope': 'Separate qualified 17-theorem status/readback context; this new core-only vector module does not import it or close its NOMT/codec/Merkle/Rust correspondence interfaces.'}}
(ROOT / 'context-reference.json').write_bytes((json.dumps(reference, indent=2, sort_keys=True) + '\n').encode())
records, payload = [], []
def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})
for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful producer source/guard provenance')
add(CURRENT / 'handwritten/TransferNullifierReaderVector01.lean', 'source/ShielddSecurity/TransferNullifierReaderVector01.lean', 'five symbolic recurrences and eight finite reusable vector proofs')
add(stdout, 'reports/fresh-13-complete-declarations.txt', 'all full raw types and standard axioms')
add(plan['owned_import_pool']['path'], 'context/empty-owned-composition-review.json', 'exact empty owned closure; fresh source has only Lean import')
add(ROOT / 'context-reference.json', 'context/context-reference.json', 'verified complete core floor and separate accepted status authentication context')
for number in [1, 2]:
    rejected_root = DIAG / ('transfer-nullifier-reader-vector-20261011-' + str(number).zfill(2))
    rejected_events = [json.loads(line) for line in (rejected_root / 'events.jsonl').read_text().splitlines()]
    assert len(rejected_events) == 2 and rejected_events[-1]['result']['status'] == 'failed'
    for name in ['prepare.py', 'plan.json', 'events.jsonl']:
        add(rejected_root / name, 'rejected-' + str(number) + '/' + name, 'original rejected proof attempt; zero credit')
    if number == 2:
        add(rejected_root / 'prepare_successor.py', 'rejected-2/prepare_successor.py', 'original failed proof repair source')
    add(rejected_root / 'handwritten/TransferNullifierReaderVector01.lean', 'rejected-' + str(number) + '/source.lean', 'exact original rejected source')
    add(rejected_root / 'runs/01-TransferNullifierReaderVector01/stdout.txt', 'rejected-' + str(number) + '/compiler-output.txt', 'full compiler output; no semantic negative-control credit')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for source in mapping['runtime_sources']:
    assert pin(source['path']) == source
    relative = Path(source['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(source['path'], 'runtime/' + relative, 'exact clean full-SHA runtime source snapshot; correspondence remains explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'full runtime SHA lock')
add(Path(__file__), 'assemble.py', 'transport assembly source')
review = {'status': 'NULLIFIER_READER_VECTOR_ALIGNMENT_PENDING_ZIP_AND_EXHAUSTIVE_UNSPENT_CHECK_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 5, 'fresh_theorem_audits': 8,
    'fresh_complete_public_audits': 13, 'fresh_audits': fresh,
    'custom_imports': 0, 'separate_upstream_status_context_reports': 17, 'context_reference': reference,
    'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'runtime_sha': mapping['runtime_sha'], 'native_test_credit': 0, 'negative_control_credit': 0,
    'rejected_attempts': 2, 'rejected_proof_credit': 0, 'certification': False, 'full_transfer': 'OPEN',
    'interfaces': mapping['interfaces'],
    'scope': mapping['scope'] + ' Successful per-input lookup map/collect derives ordered alignment and exact result length. In-place pending zip preserves vector length, including excess suffixes for mismatched inputs; success of the actual reader supplies equality rather than assuming it. A successful stage-style zipped unspent check then covers every input and derives an observed false durable flag and false current pending membership. This does not assume an unspent poststate or supplied result-length law. Lookup denotes verified status at the captured boundary; individual authentication and actual Rust Vec/iterator/store correspondence remain separate interfaces. No cache mutation, native execution, atomic evidence refresh or full Transfer closure is claimed.'}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
add(ROOT / 'review.json', 'review.json', 'complete audit, rejection, scope and explicit interfaces')
manifest = {'schema': 'transfer-reader-vector-endpoint-v1', 'entries': records,
    'fresh_audits': 13, 'custom_imports': 0, 'context_reference': reference,
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
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'), 'review': pin(ROOT / 'review.json'), 'entries': len(records), 'members': len(payload), 'fresh_audits': 13, 'native_test_credit': 0, 'certification': False}))
