"""Seal inspection facts with exact inherited source/report/guard references."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-index-inspection-20261011-02'
OLD = DIAG / 'transfer-index-inspection-20261011-01'
RAW = DIAG / 'transfer-raw-state-endpoint-20261011-01'
DELIVERY = DIAG / 'transfer-raw-delivery-endpoint-20261011-01'
CHECKPOINT = DIAG / 'transfer-index-inspection-checkpoint-20261011-01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

archive = ROOT / 'portable-windows-index-inspection-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
rejected = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == len(rejected) == 2 and events[-1]['result']['status'] == 'passed'
assert rejected[-1]['result']['status'] == 'failed'
spec = importlib.util.spec_from_file_location('index_writer_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
stdout = CURRENT / 'runs/01-TransferIndexInspectionFacts01/stdout.txt'
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 16 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for record in events[-1]['result']['objects']:
    assert pin(record['path']) == record
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 4 and len(pool['inherited_public_reports']) == 59
for selected in pool['selected']:
    for key in ['source', 'object', 'copy']:
        assert pin(selected[key]['path']) == selected[key]
raw_archive = RAW / 'portable-windows-raw-state-endpoint01.tar.xz'
delivery_archive = DELIVERY / 'portable-windows-raw-delivery-endpoint01.tar.xz'
assert pin(raw_archive)['sha256'] == 'dec82e87d6d04c87765e34ee306a9de24636bb95834e886e8dca6cfc0b82c7f8'
assert pin(delivery_archive)['sha256'] == '3da0c0cc5fb210b0b0600f82b3d6460b07b956009efd302033284772c8be85f6'
index_root = DIAG / 'transfer-index-writer-endpoint-20261011-01'
index_archive = index_root / 'portable-windows-index-writer-endpoint01.tar.xz'
assert pin(index_archive)['sha256'] == '791d8ac33050913aed3d68aaae3399a809b3565e2d8274bf8708409cac9928b2'
with tarfile.open(raw_archive, 'r:xz') as raw_tar, tarfile.open(delivery_archive, 'r:xz') as delivery_tar, tarfile.open(index_archive, 'r:xz') as index_tar:
    for selected in pool['selected']:
        if selected['module'] == 'TransferIndexWriterModel01':
            tar = index_tar
        elif selected['module'] == 'TransferRawDeliveryComposition01':
            tar = delivery_tar
        else:
            tar = raw_tar
        assert tar.extractfile('source/ShielddSecurity/' + selected['module'] + '.lean').read() == Path(selected['source']['path']).read_bytes()
    raw_review = json.loads(raw_tar.extractfile('review.json').read())
    delivery_review = json.loads(delivery_tar.extractfile('review.json').read())
    index_review = json.loads(index_tar.extractfile('review.json').read())
    assert {**raw_review['fresh_audits'], **raw_review['inherited_audits'], **delivery_review['fresh_audits'], **index_review['fresh_audits']} == pool['inherited_public_reports']
reference = {'raw': {'accepted_evidence_commit': 'ae307b2af3c98242cc6a3be82e5673d89b54f9c4', 'archive': pin(raw_archive), 'manifest': pin(RAW / 'manifest.json')},
    'delivery': {'accepted_evidence_commit': '95a570eeab095a08374e6b2a0e850be31330fc21', 'archive': pin(delivery_archive), 'manifest': pin(DELIVERY / 'manifest.json')},
    'index': {'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'archive': pin(index_archive), 'manifest': pin(index_root / 'manifest.json')},
    'inherited_complete_declarations': 59, 'inherited_sources': 4,
    'external_floor_reference': 'raw archive: context/core-floor-reference.json, accepted exact complete core floor at queue evidence 7f4abf584595911545bd8a7645e487c629931cba',
    'all_inherited_source_and_report_identities_verified': True}
(ROOT / 'inherited-reference.json').write_bytes((json.dumps(reference, indent=2, sort_keys=True) + '\n').encode())
records, payload = [], []
def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})
for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source/guard provenance')
add(CURRENT / 'handwritten/TransferIndexInspectionFacts01.lean', 'source/ShielddSecurity/TransferIndexInspectionFacts01.lean', 'handwritten finite inspection inversion, byte suffix separation and exact values')
add(stdout, 'reports/fresh-16-complete-declarations.txt', '4 definition and 12 theorem full types and standard axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete exact four-module first owned import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'exact accepted sources and full report provenance')
for name in ['prepare.py', 'plan.json', 'events.jsonl']:
    add(OLD / name, 'rejected/' + name, 'preserved first rejected source attempt; zero proof credit')
add(OLD / 'handwritten/TransferIndexInspectionFacts01.lean', 'rejected/source.lean', 'original two case-reduced proof-goal elaboration errors')
add(OLD / 'runs/01-TransferIndexInspectionFacts01/stdout.txt', 'rejected/compiler-output.txt', 'full original compiler rejection; zero negative-control credit')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'exact protected/foreign/main/clean runtime preservation')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for source in mapping['runtime_sources']:
    assert pin(source['path']) == source
    relative = Path(source['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(source['path'], 'runtime/' + relative, 'exact clean full-SHA source identity; refinement interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'full runtime SHA lock')
add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact fresh assembly derivation source')
add(Path(__file__), 'assemble.py', 'transport assembly source')
review = {'status': 'SUCCESSFUL_INDEX_OBSERVATIONS_CHECKED_INCREMENT_BYTE_TAG_SEPARATION_AND_VALUES_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 4, 'fresh_theorem_audits': 12,
    'fresh_complete_public_audits': 16, 'fresh_audits': fresh,
    'inherited_complete_public_audits': 59, 'inherited_reference': reference,
    'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'runtime_sha': mapping['runtime_sha'], 'native_test_credit': 0,
    'rejected_attempts': 1, 'rejected_proof_credit': 0, 'negative_control_credit': 0,
    'certification': False, 'full_transfer': 'OPEN', 'interfaces': mapping['interfaces'],
    'scope': mapping['scope'] + ' Inspection success recovers actual conversion, absent-ID observation, count read/decode and checked successor; next=ordinal+1 is derived and bounded below 2^64. ASCII /count, /entry/ and /id/ suffix separation is proved for arbitrary shared prefixes and appended values. Under the explicitly equality-preserving Nat projection, exact entry payload, identifier ordinal and next count writes follow from successful inspection. Conversion, duplicate and overflow refusals derive their intended model error; these proofs are not runtime negative controls. The original failed source remains zero credit.'}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
add(ROOT / 'review.json', 'review.json', 'complete result, rejected provenance, premises and precise limits')
manifest = {'schema': 'transfer-index-inspection-endpoint-v1', 'entries': records,
    'fresh_audits': 16, 'inherited_audits': 59, 'inherited_reference': reference,
    'object_bytes_in_archive': 0, 'toolchain_bytes_in_archive': 0,
    'native_test_credit': 0, 'certification': False, 'scope': review['scope']}
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
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'), 'review': pin(ROOT / 'review.json'), 'entries': len(records), 'members': len(payload), 'fresh_audits': 16, 'native_test_credit': 0, 'certification': False}))
