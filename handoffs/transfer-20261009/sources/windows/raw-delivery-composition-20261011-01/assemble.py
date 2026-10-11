"""Seal five exact successful raw-delivery composition audits, with inherited references."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-raw-delivery-composition-20261011-02'
RAW = DIAG / 'transfer-raw-state-endpoint-20261011-01'
CHECKPOINT = DIAG / 'transfer-raw-delivery-checkpoint-20261011-01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

archive = ROOT / 'portable-windows-raw-delivery-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
spec = importlib.util.spec_from_file_location('delivery_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
stdout = CURRENT / 'runs/01-TransferRawDeliveryComposition01/stdout.txt'
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 5 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for record in events[-1]['result']['objects']:
    assert pin(record['path']) == record
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 2 and len(pool['inherited_public_reports']) == 28
for selected in pool['selected']:
    for key in ['source', 'object', 'copy']:
        assert pin(selected[key]['path']) == selected[key]
accepted = RAW / 'portable-windows-raw-state-endpoint01.tar.xz'
assert pin(accepted)['sha256'] == 'dec82e87d6d04c87765e34ee306a9de24636bb95834e886e8dca6cfc0b82c7f8'
with tarfile.open(accepted, 'r:xz') as tar:
    for selected in pool['selected']:
        assert tar.extractfile('source/ShielddSecurity/' + selected['module'] + '.lean').read() == Path(selected['source']['path']).read_bytes()
    assert json.loads(tar.extractfile('review.json').read())['fresh_audits'] | json.loads(tar.extractfile('review.json').read())['inherited_audits'] == pool['inherited_public_reports']
reference = {'accepted_evidence_commit': 'ae307b2af3c98242cc6a3be82e5673d89b54f9c4',
    'archive': pin(accepted), 'manifest': pin(RAW / 'manifest.json'),
    'sources_and_complete_reports': ['source/ShielddSecurity/TransferRawStateProgram01.lean', 'source/ShielddSecurity/TransferStateDelta.lean', 'reports/fresh-16-complete-declarations.txt', 'reports/inherited-12-complete-declarations.txt'],
    'external_floor_reference': 'context/core-floor-reference.json',
    'all_inherited_source_and_report_identities_verified': True}
(ROOT / 'inherited-reference.json').write_bytes((json.dumps(reference, indent=2, sort_keys=True) + '\n').encode())
records, payload = [], []
def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})
for name in ['prepare.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful producer provenance')
add(CURRENT / 'handwritten/TransferRawDeliveryComposition01.lean', 'source/ShielddSecurity/TransferRawDeliveryComposition01.lean', 'handwritten symbolic success composition')
add(stdout, 'reports/fresh-5-complete-declarations.txt', 'five full raw theorem types and standard axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete exact two-module first owned import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified accepted source/report/floor reference')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'exact read-only preservation checkpoint')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA lock')
add(Path(__file__), 'assemble.py', 'transport assembly source')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
review = {'status': 'RAW_SUCCESS_CACHE_AND_DELIVERY_INDEX_MODE_COMPOSITION_QUALIFIED',
    'fresh_sources': 1, 'fresh_complete_public_audits': 5, 'fresh_audits': fresh,
    'inherited_complete_public_audits': 28, 'inherited_reference': reference,
    'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'runtime_sha': mapping['runtime_sha'], 'native_test_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'unsealed_preparation_failure': 'The 01 preparation attempted dictionary concatenation and failed before plan admission or Lean launch. The fresh 02 generator merges the two complete audit dictionaries; source is byte-identical. No proof or negative-control credit for preparation failure.',
    'scope': mapping['scope'] + ' The five derived successes recover the actual raw outcome, retain original parent/index callback observations, apply the selected child cache, preserve events and derive exact deferred append or PerTx unchanged queue. The index callback remains an explicit interface and its cache framing is a separate obligation; this packet does not close that obligation.'}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
add(ROOT / 'review.json', 'review.json', 'complete audit and precise scope')
manifest = {'schema': 'transfer-raw-delivery-endpoint-v1', 'entries': records,
    'fresh_audits': 5, 'inherited_audits': 28, 'inherited_reference': reference,
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
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'), 'review': pin(ROOT / 'review.json'), 'entries': len(records), 'members': len(payload), 'fresh_audits': 5, 'native_test_credit': 0, 'certification': False}))
