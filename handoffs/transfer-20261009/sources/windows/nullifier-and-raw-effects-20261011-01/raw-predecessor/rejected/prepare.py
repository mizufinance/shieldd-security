"""Prepare finite raw effect ordering on the exact four-module closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
BATCH = DIAG / 'transfer-nullifier-batch-source-20261011-02'
POOL = DIAG / 'transfer-raw-effects-owned-floor-20261011-02'
MODULE = 'TransferRawEffectsSource01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

assert not (ROOT / 'plan.json').exists() and not POOL.exists()
runner = ROOT / 'execute_bounded.py'
assert pin(BATCH / runner.name)['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(BATCH / runner.name, runner)
spec = importlib.util.spec_from_file_location('raw_effects_complete_auditor', runner)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((BATCH / 'plan.json').read_bytes())
old_pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
records = [(r['module'], r['source'], r['object']) for r in old_pool['selected']]
inputs = old_pool['input_records'][:]
audits = dict(old_pool['inherited_public_reports'])
events = [json.loads(s) for s in (BATCH / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
target = plan['targets'][0]
stdout = BATCH / 'runs/01-TransferNullifierBatchSource01/stdout.txt'
batch_audits = m.audit(stdout.read_text(), target['audit_names'])
assert len(batch_audits) == 16 and batch_audits == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
assert set(audits).isdisjoint(batch_audits)
audits.update(batch_audits)
records.append(('TransferNullifierBatchSource01', target['source'], events[-1]['result']['objects'][0]))
inputs += [pin(BATCH / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferNullifierBatchSource01.lean', 'project/ShielddSecurity/TransferNullifierBatchSource01.lean']]
inputs.append(pin(stdout))
assert len(records) == 4 and len(audits) == 57
POOL.mkdir()
selected = []
for module, source, obj in records:
    assert pin(source['path']) == source and pin(obj['path']) == obj
    copy = POOL / 'modules/ShielddSecurity' / (module + '.olean')
    copy.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(obj['path'], copy)
    assert pin(copy)['sha256'] == obj['sha256']
    selected.append({'module': module, 'source': source, 'object': obj, 'copy': pin(copy)})
    inputs += [source, obj]
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 4, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete four-module first owned root; 57 inherited full reports. Exact copying adds no replay or Rust refinement.'}
composition_file = POOL / 'composition-review.json'
dump(composition_file, composition)
handwritten = ROOT / 'handwritten' / (MODULE + '.lean')
source = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 27 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', source, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(source))
target_source = ROOT / 'project/ShielddSecurity' / handwritten.name
target_source.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target_source)
runtime = Path('C:/src/shieldd-pr160-844389ee')
mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / n) for n in ['crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
        'crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs',
        'crates/core/component/shielded-pool/src/component/shielded_pool.rs',
        'crates/core/component/shielded-pool/src/component/note_manager.rs',
        'crates/core/component/shielded-pool/src/state_key.rs', 'crates/core/component/sct/src/component/tree.rs']],
    'interfaces': ['Captured note source and reacquired ordinary volume source are explicit callback arguments; exact validated capability comparison/stateless re-extraction is represented by exactMatched; proof cryptography remains separate',
        'Current source Option Bool preserves missing versus present nontransaction source; actual source codec/identity remains explicit',
        'Qualified nullifier backend getter, status authentication, equality, collections and machine capacity interfaces remain inherited',
        'Note/SCT and volume payload insertion are failure-aware callbacks and may emit internal events or retain partial cache changes',
        'Volume read is the current child overlay observation; concrete day/nullifier key projection and verifiable get/put byte correspondence remain explicit',
        'Distinct entry/day projected keys is explicit for exact final values; no hash semantic correspondence or native durability inferred',
        'Event encoding, Rust ownership, Clone/COW and mutable/cache correspondence remain explicit'],
    'scope': 'Functional post-capability raw Transfer source order, all spend event loop, note callback/event ordering, ordinary late volume recheck, exact two verifiable marker writes, and derived enclosing delivery rejection/parent-and-queue preservation. Concrete callback SCT/Merkle behavior and native controls remain open. No runtime/negative-control credit, atomic evidence refresh or full Transfer certification.'}
mapping_file = ROOT / 'source-mapping.json'
dump(mapping_file, mapping)
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': MODULE, 'source': pin(target_source), 'predecessor_source': pin(handwritten),
    'imports': ['ShielddSecurity.TransferNullifierBatchSource01'],
    'audit_names': ['ShielddSecurity.' + MODULE + '.' + n for n in names]}]
baseline = json.loads(Path(plan['preservation']['path']).read_bytes())
plan['pins'] = baseline['protected'] + baseline['foreign'] + inputs + plan['owned_imports']
plan['pins'] += [pin(p) for p in [Path(__file__), ROOT / 'prepare_successor.py', runner, handwritten, target_source, composition_file, mapping_file]]
plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'RAW_TRANSFER_SOURCE_ORDER_SEMANTIC_EVENTS_AND_LATE_VOLUME_RECHECK'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh 02 exposes captured source callback arguments and composes the actual late-conflict error with enclosing delivery. Successful 01 source/reports preserved unchanged as scoped prior evidence; not re-imported or counted as a fresh ancestor.'
plan['artifact_policy'] = 'One source and bounded reports/object; complete four-module first owned root and reachable core floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit guards unchanged.'
plan['invocation'] = 'Autonomous serial narrow raw effect proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'RAW_EFFECT_SOURCE_AND_COMPLETE_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 27, 'inherited_audits': 57, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
dump(ROOT / 'review.json', review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
