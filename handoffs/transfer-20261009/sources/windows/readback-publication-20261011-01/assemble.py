"""Seal exact three-source replay evidence; references reuse accepted core bytes."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-readback-recovery-publication-20261010-02'
QUEUE = DIAG / 'transfer-deferred-queue-endpoint-20261010-01'
CHECKPOINT = DIAG / 'transfer-publication-model-checkpoint-20261010-01'
def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
archive = ROOT / 'portable-windows-readback-publication-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(line) for line in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 6 and len(plan['targets']) == 3
spec = importlib.util.spec_from_file_location('readback_publication_full_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
fresh = []
results = []
for i, target in enumerate(plan['targets'], 1):
    started, finished = events[2*i-2:2*i]
    assert started['event'] == 'attempt_started' and finished['event'] == 'attempt_finished'
    assert started['module'] == finished['module'] == target['module']
    result = finished['result']
    assert result['status'] == 'passed'
    stdout = CURRENT / ('runs/%02d-%s/stdout.txt' % (i, target['module']))
    audited = m.audit(stdout.read_text(), target['audit_names'])
    assert audited == result['audits'] and pin(stdout) == result['stdout']
    assert pin(target['source']['path']) == target['source']
    assert pin(target['predecessor_source']['path']) == target['predecessor_source']
    assert target['source']['sha256'] == target['predecessor_source']['sha256']
    for record in result['objects']:
        assert pin(record['path']) == record
    fresh += audited
    results.append(result)
assert len(fresh) == 35 and [len(r['audits']) for r in results] == [17, 10, 8]
assert 'stderr=subprocess.STDOUT' in (CURRENT / 'execute_bounded.py').read_text()
floor = plan['external_floor']
assert pin(floor['path']) == {key: floor[key] for key in ['path', 'bytes', 'sha256']}
assert floor['sha256'] == 'a3664457d8083b4ce0c690e9da346596e4d5bb8bc142d34ef7c326936101d0c5'
accepted_archive = QUEUE / 'portable-windows-deferred-queue-endpoint01.tar.xz'
assert pin(accepted_archive)['sha256'] == 'eb830a8f56cd6927904dcf1564f4f53527863ab90dca0e8189f5c6c2ef250033'
with tarfile.open(accepted_archive, 'r:xz') as tar:
    assert tar.extractfile('context/core-external-floor.json').read() == Path(floor['path']).read_bytes()
reference = {'kind': 'EXACT_PREVIOUSLY_ACCEPTED_COMPLETE_CORE_FLOOR_BYTES',
    'original': floor, 'accepted_archive': pin(accepted_archive),
    'accepted_manifest': pin(QUEUE / 'manifest.json'),
    'accepted_evidence_commit': '7f4abf584595911545bd8a7645e487c629931cba',
    'accepted_archive_path': 'context/core-external-floor.json',
    'all_original_bytes_verified_equal': True,
    'scope': 'The same complete 2141-module reachable Lean/Init core floor was used and rehashed by the unchanged guarded replay. Its exact metadata bytes are already in the accepted queue endpoint; this transport references those original bytes instead of duplicating six MiB of unchanged metadata. No toolchain or object bytes are transported.'}
(ROOT / 'core-floor-reference.json').write_bytes((json.dumps(reference, indent=2, sort_keys=True) + '\n').encode())
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
payload, records = [], []
def add(p, relative, role):
    p = Path(p)
    assert relative not in {name for name, _ in payload}
    payload.append((relative, p.read_bytes()))
    records.append({'archive_path': relative, 'original': pin(p), 'role': role})
for name in ['prepare.py', 'execute_bounded.py', 'plan.json', 'review.json', 'events.jsonl', 'source-mapping.json']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful fresh producer recipe and provenance')
for i, target in enumerate(plan['targets'], 1):
    add(target['source']['path'], 'source/ShielddSecurity/' + target['module'] + '.lean', 'byte-identical existing handwritten qualified source')
    add(CURRENT / ('runs/%02d-%s/stdout.txt' % (i, target['module'])),
        'reports/' + target['module'] + '-complete-types-and-axioms.txt', 'complete raw public theorem types and standard axioms')
add(plan['owned_import_pool']['path'], 'context/empty-owned-composition-review.json', 'exact empty imported-owned-object floor; targets compiled in dependency order')
add(ROOT / 'core-floor-reference.json', 'context/core-floor-reference.json', 'exact accepted complete external closure association')
add(CHECKPOINT / 'preservation_check.py', 'preservation/preservation_check.py', 'unchanged independent preservation recipe')
add(CHECKPOINT / 'preservation.json', 'preservation/preservation.json', 'all seventy-one protected and sixty-five foreign files retained')
for source in mapping['runtime_sources']:
    assert pin(source['path']) == source
    relative = Path(source['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(source['path'], 'runtime/' + relative, 'exact clean full-SHA runtime source snapshot; semantic refinement remains an interface')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA lock')
add(Path(__file__), 'assemble.py', 'exact sealing and transport recipe')
review = {'status': 'EXISTING_READBACK_RECOVERY_WRITER_PUBLICATION_MODELS_FRESHLY_QUALIFIED',
    'sources': 3, 'new_source_changes': 0, 'complete_public_theorem_audits': 35,
    'per_module_audits': {'TransferReadback': 17, 'TransferBankRecovery': 10, 'TransferWriterPublication': 8},
    'audits': fresh, 'compiler_results': results,
    'lean_seconds': sum(r['seconds'] for r in results), 'runtime_sha': mapping['runtime_sha'],
    'current_plan': pin(CURRENT / 'plan.json'), 'physical_guard_runner': pin(CURRENT / 'execute_bounded.py'),
    'native_test_credit': 0, 'negative_control_credit': 0, 'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' Fresh complete type and standard-axiom reports for all thirty-five theorems; no theorem or model definition changed. The model hostIdle function is a returned-success observation and is not a complete model of concrete Host phases. Capacity failure after writer Ready is explicitly retained. The accepted finite native controls remain separate runtime evidence.'}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
add(ROOT / 'review.json', 'review.json', 'independent full raw report, scope and source identity review')
manifest = {'schema': 'transfer-readback-publication-endpoint-v1', 'entries': records,
    'sources': 3, 'new_source_changes': 0, 'complete_public_theorem_audits': 35,
    'external_floor_reference': reference, 'object_bytes_in_archive': 0, 'toolchain_bytes_in_archive': 0,
    'native_test_credit': 0, 'certification': False, 'scope': review['scope']}
data = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
(ROOT / 'manifest.json').write_bytes(data)
payload.append(('manifest.json', data))
with tarfile.open(archive, 'w:xz', preset=6) as tar:
    for relative, data in sorted(payload):
        info = tarfile.TarInfo(relative)
        info.size, info.mode, info.mtime = len(data), 0o644, 0
        tar.addfile(info, io.BytesIO(data))
with tarfile.open(archive, 'r:xz') as tar:
    assert len(tar.getmembers()) == len(payload)
    assert all(tar.extractfile(name).read() == data for name, data in payload)
assert all(pin(r['original']['path']) == r['original'] for r in records)
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'),
    'review': pin(ROOT / 'review.json'), 'entries': len(records), 'archive_members': len(payload),
    'sources': 3, 'complete_public_theorem_audits': 35, 'native_test_credit': 0, 'certification': False}))
