"""Seal complete failure-aware raw state program audits and rejected predecessor."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-raw-state-program-20261011-02'
OLD = DIAG / 'transfer-raw-state-program-20261011-01'
QUEUE = DIAG / 'transfer-deferred-queue-endpoint-20261010-01'
INHERITED = DIAG / 'transfer-implementation-20261002/state-delta-kernel-3020'
CHECKPOINT = DIAG / 'transfer-raw-state-checkpoint-20261011-01'
def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
archive = ROOT / 'portable-windows-raw-state-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
rejected = [json.loads(s) for s in (OLD / 'events.jsonl').read_text().splitlines()]
assert len(events) == len(rejected) == 2 and events[-1]['result']['status'] == 'passed'
assert rejected[-1]['result']['status'] == 'failed'
assert len(plan['targets']) == 1 and len(plan['targets'][0]['audit_names']) == 16
spec = importlib.util.spec_from_file_location('raw_state_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
stdout = CURRENT / 'runs/01-TransferRawStateProgram01/stdout.txt'
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert fresh == events[-1]['result']['audits'] and pin(stdout) == events[-1]['result']['stdout']
for record in events[-1]['result']['objects']:
    assert pin(record['path']) == record
legacy = json.loads((INHERITED / 'manifest.json').read_bytes())
inherited = m.audit((INHERITED / 'stdout.txt').read_text(),
    ['ShielddSecurity.TransferStateDelta.' + n for n in legacy['theorems']])
assert len(inherited) == 12
for name in ['exit.txt', 'lean-exit.txt']:
    assert (INHERITED / name).read_text().strip() == '0'
accepted_archive = QUEUE / 'portable-windows-deferred-queue-endpoint01.tar.xz'
assert pin(accepted_archive)['sha256'] == 'eb830a8f56cd6927904dcf1564f4f53527863ab90dca0e8189f5c6c2ef250033'
floor = plan['external_floor']
assert floor['sha256'] == 'a3664457d8083b4ce0c690e9da346596e4d5bb8bc142d34ef7c326936101d0c5'
with tarfile.open(accepted_archive, 'r:xz') as tar:
    assert tar.extractfile('context/core-external-floor.json').read() == Path(floor['path']).read_bytes()
reference = {'kind': 'EXACT_ACCEPTED_COMPLETE_CORE_FLOOR_BYTES', 'original': floor,
    'accepted_archive': pin(accepted_archive), 'accepted_manifest': pin(QUEUE / 'manifest.json'),
    'accepted_evidence_commit': '7f4abf584595911545bd8a7645e487c629931cba',
    'accepted_archive_path': 'context/core-external-floor.json', 'all_original_bytes_verified_equal': True}
(ROOT / 'core-floor-reference.json').write_bytes((json.dumps(reference, indent=2, sort_keys=True) + '\n').encode())
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
payload, records = [], []
def add(p, relative, role):
    p = Path(p)
    assert relative not in {n for n, _ in payload}
    payload.append((relative, p.read_bytes()))
    records.append({'archive_path': relative, 'original': pin(p), 'role': role})
for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'events.jsonl', 'review.json', 'source-mapping.json']:
    add(CURRENT / name, 'qualified/' + name, 'exact fresh successful producer provenance')
add(CURRENT / 'handwritten/TransferRawStateProgram01.lean', 'source/ShielddSecurity/TransferRawStateProgram01.lean', 'qualified failure-aware handwritten symbolic program')
add(stdout, 'reports/fresh-16-complete-declarations.txt', 'complete fresh raw types and standard-axiom reports')
add(INHERITED / 'project/ShielddSecurity/TransferStateDelta.lean', 'source/ShielddSecurity/TransferStateDelta.lean', 'exact unchanged accepted cache/delivery model')
add(INHERITED / 'stdout.txt', 'reports/inherited-12-complete-declarations.txt', 'complete inherited raw types and standard axioms; no new replay')
for name in ['manifest.json', 'audit.json', 'recipe.json', 'exit.txt', 'lean-exit.txt', 'complete.txt']:
    add(INHERITED / name, 'inherited/' + name, 'exact accepted inherited qualifier provenance')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'exact complete one-object first owned package; object bytes excluded')
add(ROOT / 'core-floor-reference.json', 'context/core-floor-reference.json', 'exact complete external floor already carried by accepted endpoint')
for name in ['prepare.py', 'plan.json', 'events.jsonl']:
    add(OLD / name, 'rejected/' + name, 'rejected predecessor; zero proof/control credit')
add(OLD / 'handwritten/TransferRawStateProgram01.lean', 'rejected/source.lean', 'rejected reserved binders/lint; unchanged model/theorem contracts under alpha repair')
add(OLD / 'runs/01-TransferRawStateProgram01/stdout.txt', 'rejected/compiler-output.txt', 'original rejected compiler output; no negative-control credit')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'exact independent preservation checkpoint')
for source in mapping['runtime_sources']:
    assert pin(source['path']) == source
    relative = Path(source['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(source['path'], 'runtime/' + relative, 'exact clean full-SHA source snapshot; correspondence interfaces remain explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime commit lock')
add(Path(__file__), 'assemble.py', 'exact transport assembly recipe')
review = {'status': 'SCOPED_FAILURE_AWARE_RAW_CHILD_CACHE_PROGRAM_AND_DELIVERY_COMPOSITION_QUALIFIED',
    'fresh_sources': 1, 'fresh_complete_public_audits': 16,
    'inherited_sources': 1, 'inherited_complete_public_audits': 12,
    'fresh_audits': fresh, 'inherited_audits': inherited,
    'compiler_result': events[-1]['result'], 'current_plan': pin(CURRENT / 'plan.json'),
    'physical_guard_runner': pin(CURRENT / 'execute_bounded.py'),
    'rejected_predecessors': 1, 'rejected_proof_credit': 0, 'negative_control_credit': 0,
    'native_test_credit': 0, 'certification': False, 'full_transfer': 'OPEN',
    'runtime_sha': mapping['runtime_sha'],
    'scope': mapping['scope'] + ' Sixteen complete fresh declaration reports. Raw errors retain the failing callback cache and suppress arbitrary suffixes; successful-prefix composition is symbolic. Error-to-Option projection rejects delivery before index/apply/queue append and derives enclosing parent/queue preservation without a raw rollback or desired poststate premise. Callback-result premises are explicit program facts. Existing finite late-delivery controls and the new unexecuted delayed/Host controls are not conflated.'}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
add(ROOT / 'review.json', 'review.json', 'complete raw audit, rejection, provenance and scope review')
manifest = {'schema': 'transfer-raw-state-endpoint-v1', 'entries': records,
    'fresh_audits': 16, 'inherited_audits': 12, 'external_floor_reference': reference,
    'object_bytes_in_archive': 0, 'toolchain_bytes_in_archive': 0, 'native_test_credit': 0,
    'certification': False, 'scope': review['scope']}
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
    assert all(tar.extractfile(n).read() == data for n, data in payload)
assert all(pin(r['original']['path']) == r['original'] for r in records)
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'),
    'review': pin(ROOT / 'review.json'), 'entries': len(records), 'archive_members': len(payload),
    'fresh_audits': 16, 'inherited_audits': 12, 'native_test_credit': 0, 'certification': False}))
