"""Seal exact retained producer bytes and scoped audit accounting; no replay."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-deferred-queue-model-20261010-03'
INHERITED = DIAG / 'transfer-implementation-20261002/state-delta-kernel-3020'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

archive = ROOT / 'portable-windows-deferred-queue-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(line) for line in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
assert len(plan['targets']) == 1 and len(plan['targets'][0]['audit_names']) == 17
spec = importlib.util.spec_from_file_location('deferred_queue_full_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
stdout = CURRENT / 'runs/01-TransferDeferredQueueSourceModel01/stdout.txt'
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert fresh == events[-1]['result']['audits'] and pin(stdout) == events[-1]['result']['stdout']
assert 'stderr=subprocess.STDOUT' in (CURRENT / 'execute_bounded.py').read_text()
for record in events[-1]['result']['objects']:
    assert pin(record['path']) == record
legacy_manifest = json.loads((INHERITED / 'manifest.json').read_bytes())
legacy_names = ['ShielddSecurity.TransferStateDelta.' + n for n in legacy_manifest['theorems']]
inherited = m.audit((INHERITED / 'stdout.txt').read_text(), legacy_names)
assert len(inherited) == 12
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
payload = []
records = []

def add(p, relative, role):
    p = Path(p)
    data = p.read_bytes()
    assert relative not in {name for name, _ in payload}
    payload.append((relative, data))
    records.append({'archive_path': relative, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'events.jsonl', 'source-mapping.json']:
    add(CURRENT / name, 'qualified/' + name, 'exact fresh producer recipe/plan/report provenance')
add(CURRENT / 'handwritten/TransferDeferredQueueSourceModel01.lean', 'source/ShielddSecurity/TransferDeferredQueueSourceModel01.lean', 'fresh handwritten qualified model')
add(stdout, 'reports/fresh-17-complete-declarations.txt', 'complete fresh type and standard-axiom output')
add(INHERITED / 'project/ShielddSecurity/TransferStateDelta.lean', 'source/ShielddSecurity/TransferStateDelta.lean', 'unchanged retained core cache model')
for name in ['manifest.json', 'audit.json', 'recipe.json', 'exit.txt', 'lean-exit.txt', 'complete.txt']:
    add(INHERITED / name, 'inherited/' + name, 'exact inherited qualifier provenance; no new replay')
add(INHERITED / 'stdout.txt', 'reports/inherited-12-complete-declarations.txt', 'complete retained type and standard-axiom output')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete one-object first-package association; object bytes excluded')
add(plan['external_floor']['path'], 'context/core-external-floor.json', 'complete exact core-only transitive source/object pin records; artifacts excluded')
for i in [1, 2]:
    predecessor = DIAG / ('transfer-deferred-queue-model-20261010-%02d' % i)
    rejected = [json.loads(line) for line in (predecessor / 'events.jsonl').read_text().splitlines()]
    assert rejected[-1]['result']['status'] == 'failed'
    for name in ['plan.json', 'events.jsonl']:
        add(predecessor / name, 'rejected/%02d/' % i + name, 'failed predecessor, zero proof/control credit')
    add(predecessor / 'handwritten/TransferDeferredQueueSourceModel01.lean', 'rejected/%02d/source.lean' % i, 'rejected source, zero proof/control credit')
    add(predecessor / 'runs/01-TransferDeferredQueueSourceModel01/stdout.txt', 'rejected/%02d/compiler-output.txt' % i, 'failure diagnostic, zero proof/control credit')
for source in mapping['runtime_sources']:
    assert pin(source['path']) == source
    relative = 'runtime/' + str(Path(source['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee'))).replace(chr(92), '/')
    add(source['path'], relative, 'exact clean full-SHA source snapshot; control flow reviewed, no Rust refinement proof')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime commit lock')
add(Path(__file__), 'assemble.py', 'sealed transport recipe')
review = {
    'status': 'SCOPED_DEFERRED_QUEUE_SOURCE_ORDER_MODEL_QUALIFIED',
    'fresh_sources': 1, 'fresh_complete_public_audits': 17,
    'inherited_sources': 1, 'inherited_complete_public_audits': 12,
    'fresh_audits': fresh, 'inherited_audits': inherited,
    'rejected_predecessors': 2, 'rejected_proof_credit': 0, 'negative_control_credit': 0,
    'runtime_sha': mapping['runtime_sha'],
    'current_plan': pin(CURRENT / 'plan.json'), 'compiler_output': pin(stdout),
    'compiler_result': events[-1]['result'],
    'physical_guard_runner': pin(CURRENT / 'execute_bounded.py'),
    'scope': 'Universal functional control-flow/cache model only. Exclusive acquisition and height read errors precede queue consumption; index-write error after take discards new child state/events while consuming queue; an empty same-instance flush retry cannot recover those entries. Outcome.events denotes additions from this flush, not the entire prior event history. Success applies the index child cache to the original parent. No target equality premise, native execution, compiler-failure control credit, Rust cache/ownership/codec/index callback refinement, Host durable publication/retry safety, or full Transfer certification is claimed.',
    'native_test_credit': 0, 'certification': False,
    'full_transfer': 'OPEN',
}
review_data = (json.dumps(review, indent=2, sort_keys=True) + '\n').encode()
(ROOT / 'review.json').write_bytes(review_data)
add(ROOT / 'review.json', 'review.json', 'scoped independent raw report/identity review')
manifest = {'schema': 'transfer-deferred-queue-endpoint-v1', 'entries': records,
    'fresh_audits': 17, 'inherited_audits': 12, 'object_bytes_in_archive': 0,
    'toolchain_bytes_in_archive': 0, 'native_test_credit': 0, 'certification': False,
    'scope': review['scope']}
manifest_data = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
(ROOT / 'manifest.json').write_bytes(manifest_data)
payload.append(('manifest.json', manifest_data))
with tarfile.open(archive, 'w:xz', preset=6) as tar:
    for relative, data in sorted(payload):
        info = tarfile.TarInfo(relative)
        info.size = len(data)
        info.mode = 0o644
        info.mtime = 0
        tar.addfile(info, io.BytesIO(data))
with tarfile.open(archive, 'r:xz') as tar:
    assert len(tar.getmembers()) == len(payload)
    for name, data in payload:
        assert tar.extractfile(name).read() == data
for record in records:
    assert pin(record['original']['path']) == record['original']
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'),
    'review': pin(ROOT / 'review.json'), 'entries': len(records), 'archive_members': len(payload),
    'fresh_audits': 17, 'inherited_audits': 12, 'native_test_credit': 0, 'certification': False}))
