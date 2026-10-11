"""Prepare batch staging against exact cache/raw and reader-vector qualified objects."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
RAW = DIAG / 'transfer-raw-state-program-20261011-02'
VECTOR = DIAG / 'transfer-nullifier-reader-vector-20261011-03'
POOL = DIAG / 'transfer-nullifier-batch-owned-floor-20261011-02'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

assert not (ROOT / 'plan.json').exists() and not POOL.exists()
runner = ROOT / 'execute_bounded.py'
assert pin(RAW / runner.name)['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(RAW / runner.name, runner)
spec = importlib.util.spec_from_file_location('nullifier_batch_exact_auditor', runner)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((RAW / 'plan.json').read_bytes())
existing = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
records = [(r['module'], r['source'], r['object']) for r in existing['selected']]
inputs = existing['input_records'][:]
audits = dict(existing['inherited_public_reports'])
for directory, module, count in [(RAW, 'TransferRawStateProgram01', 16), (VECTOR, 'TransferNullifierReaderVector01', 13)]:
    producer = json.loads((directory / 'plan.json').read_bytes())
    events = [json.loads(line) for line in (directory / 'events.jsonl').read_text().splitlines()]
    assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
    target = producer['targets'][0]
    stdout = directory / ('runs/01-' + module + '/stdout.txt')
    current = m.audit(stdout.read_text(), target['audit_names'])
    assert len(current) == count and current == events[-1]['result']['audits']
    assert set(current).isdisjoint(audits)
    audits.update(current)
    records.append((module, target['source'], events[-1]['result']['objects'][0]))
    inputs += [pin(directory / name) for name in ['plan.json', 'events.jsonl', 'execute_bounded.py',
        'source-mapping.json', 'handwritten/' + module + '.lean', 'project/ShielddSecurity/' + module + '.lean']]
    inputs.append(pin(stdout))
assert len(records) == 3 and len(audits) == 41
selected = []
POOL.mkdir()
for module, source, obj in records:
    assert pin(source['path']) == source and pin(obj['path']) == obj
    copy = POOL / 'modules/ShielddSecurity' / (module + '.olean')
    copy.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(obj['path'], copy)
    assert pin(copy)['sha256'] == obj['sha256']
    selected.append({'module': module, 'source': source, 'object': obj, 'copy': pin(copy)})
    inputs += [source, obj]
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 3, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete exact first owned package for cache/raw outcome plus reader-vector closure. Forty-one full inherited declarations checked; copying qualified objects adds no new replay or Rust refinement.'}
composition_file = POOL / 'composition-review.json'
composition_file.write_bytes((json.dumps(composition, indent=2, sort_keys=True) + '\n').encode())
handwritten = ROOT / 'handwritten/TransferNullifierBatchSource01.lean'
source = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 16 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', source, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(source))
target = ROOT / 'project/ShielddSecurity' / handwritten.name
target.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target)
runtime = Path('C:/src/shieldd-pr160-844389ee')
mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / name) for name in ['crates/core/component/sct/src/component/tree.rs',
        'crates/core/component/sct/src/state_key.rs', 'crates/core/component/sct/src/permanent_nullifiers/store.rs',
        'crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs']],
    'order': 'Public nullify_all returns immediately for empty input. Nonempty input requires source.id().is_some(), then the check_durable=true stage checks local duplicate insertion, Open pending block, saturating capacity, current pending membership, authenticated complete vector and zipped unspent flags before one pending-block object_put.',
    'capacity': 'Nat.min(sum,wordMax) models usize saturating_add. If capacity<wordMax, success derives the exact natural sum bound; capacity/source machine-width correspondence is explicit, not silently assumed.',
    'cache': 'Error retains the supplied input cache, which can contain earlier raw effects. Nonempty success derives one explicit pending object update; verifiable/NV/events and every other object key are framed. No whole-handler rollback assertion.',
    'interfaces': ['Decoded nullifier equality and BTreeSet/OrdSet/Vector correspondence', 'Pending getter is the current child snapshot, including default Open and sealed representation', 'Source-id boolean and usize wordMax/capacity reflect the pinned runtime', 'Individually verified lookup/reader gate at the captured committed boundary; current pending join supplied by the qualified vector program', 'Typed pending-object encoding, object-key projection, Clone/COW/ownership and Rust cache correspondence', 'Concrete SCT/note insertion and durability remain separate'],
    'scope': 'Functional public nullifier-batch source-order and exact single object-write proof only. Existing finite SCT and genuine delivery controls are separate evidence; new genuine delayed/queue controls remain unrun. No new native or negative-control execution credit, no atomic evidence refresh or full Transfer certification.'}
mapping_file = ROOT / 'source-mapping.json'
mapping_file.write_bytes((json.dumps(mapping, indent=2, sort_keys=True) + '\n').encode())
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': 'TransferNullifierBatchSource01', 'source': pin(target),
    'predecessor_source': pin(handwritten), 'imports': ['ShielddSecurity.TransferRawStateProgram01', 'ShielddSecurity.TransferNullifierReaderVector01'],
    'audit_names': ['ShielddSecurity.TransferNullifierBatchSource01.' + name for name in names]}]
baseline = json.loads(Path(plan['preservation']['path']).read_bytes())
plan['pins'] = baseline['protected'] + baseline['foreign'] + inputs + plan['owned_imports']
plan['pins'] += [pin(p) for p in [Path(__file__), ROOT / 'prepare_successor.py', runner, handwritten, target, composition_file, mapping_file]]
plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'PUBLIC_NULLIFIER_BATCH_SOURCE_ORDER_COMPLETE_DURABLE_CHECK_AND_EXACT_PENDING_OBJECT_WRITE'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh 02 after preserved 01 proof elaboration failure: normalize Nat.min to its standard instance, let simplification produce the two exact equalities, and parenthesize boolean-or equality. Definitions, premises and theorem conclusions unchanged; rejected attempt zero credit; guards/audits unchanged.'
plan['artifact_policy'] = 'One source and bounded receipts/object, exact three-module complete first owned root and complete reachable core floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit protections unchanged.'
plan['invocation'] = 'Autonomous serial narrow public batch proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'SOURCE_AND_COMPLETE_THREE_MODULE_OWNED_ROOT_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 16, 'inherited_audits': 41, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
