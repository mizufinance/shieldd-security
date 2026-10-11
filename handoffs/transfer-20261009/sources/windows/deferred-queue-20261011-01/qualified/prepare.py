"""One named queue-order proof over the retained, audited core cache model."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
D = DIAG / 'transfer-implementation-20261002'
OLD = D / 'state-delta-kernel-3020'
PRIOR = DIAG / 'transfer-proof-admission-20261010-02'
POOL = DIAG / 'transfer-deferred-queue-owned-floor-20261010-03'

def pin(p):
    p = Path(p)
    return {'path': str(p), 'bytes': p.stat().st_size,
            'sha256': hashlib.file_digest(p.open('rb'), 'sha256').hexdigest()}

assert not (ROOT / 'plan.json').exists() and not POOL.exists()
runner = ROOT / 'execute_bounded.py'
assert pin(PRIOR / runner.name)['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(PRIOR / runner.name, runner)
spec = importlib.util.spec_from_file_location('queue_exact_auditor', runner)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
previous = json.loads((OLD / 'manifest.json').read_bytes())
names = ['ShielddSecurity.TransferStateDelta.' + n for n in previous['theorems']]
assert len(names) == 12
audited = m.audit((OLD / 'stdout.txt').read_text(), names)
for name in ['exit.txt', 'lean-exit.txt']:
    assert (OLD / name).read_text().strip() == '0'
assert not (OLD / 'stderr.txt').read_bytes()
source = OLD / 'project/ShielddSecurity/TransferStateDelta.lean'
assert pin(source)['sha256'] == previous['sha256'] == '8f618a379a625f4cf3a8d0d016ef25ccc63d4e9416a618e508412b1861262997'
assert pin(Path(previous['source']))['sha256'] == previous['sha256']
assert 'set_option maxHeartbeats 200000' in source.read_text()
obj = OLD / 'project/ShielddSecurity/TransferStateDelta.olean'
POOL.mkdir()
destination = POOL / 'modules/ShielddSecurity/TransferStateDelta.olean'
destination.parent.mkdir(parents=True)
shutil.copyfile(obj, destination)
assert pin(destination)['sha256'] == pin(obj)['sha256']
inputs = [pin(OLD / n) for n in ['manifest.json', 'audit.json', 'stdout.txt', 'stderr.txt', 'exit.txt', 'lean-exit.txt', 'complete.txt', 'recipe.json']]
inputs += [pin(source), pin(obj), pin(Path(previous['source']))]
composition = {
    'admission_ready': True, 'kernel_credit': 0, 'objects': 1,
    'selected': [{'module': 'TransferStateDelta', 'source': pin(source), 'object': pin(obj), 'copy': pin(destination)}],
    'input_records': inputs, 'inherited_public_reports': audited,
    'charged_new_object_bytes': destination.stat().st_size,
    'scope': 'Exact one-module core-only import closure; twelve retained complete public type/standard-axiom reports and both zero exits checked. Copy establishes identity only; no replay or Rust/source/durability refinement credit.',
}
composition_file = POOL / 'composition-review.json'
composition_file.write_bytes((json.dumps(composition, indent=2, sort_keys=True) + '\n').encode())
handwritten = ROOT / 'handwritten/TransferDeferredQueueSourceModel01.lean'
text = handwritten.read_text()
new_names = ['ShielddSecurity.TransferDeferredQueueSourceModel01.' + n
    for n in re.findall(r'^(?:inductive|structure|abbrev|def|theorem) ([A-Za-z0-9_]+)', text, re.M)]
assert len(new_names) == 17
assert re.findall(r'^#check @([^\n]+)', text, re.M) == new_names
assert re.findall(r'^#print axioms ([^\n]+)', text, re.M) == new_names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(text))
target = ROOT / 'project/ShielddSecurity' / handwritten.name
target.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target)
runtime = Path('C:/src/shieldd-pr160-844389ee')
mapping = {
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / p) for p in ['crates/core/app/src/app/mod.rs', 'crates/core/app/src/app/host.rs']],
    'ordering': ['non-deferred/empty early success', 'exclusive child acquisition', 'height read', 'take entire deferred queue', 'fallible sequential index writes', 'apply child only after every write succeeds'],
    'panic_phase': 'App.end_block expects successful flush before Host.end_block writes CommitInterrupted. A flush panic therefore leaves the Host phase InBlock.',
    'scope': 'Hand-reviewed control-flow correspondence and generic cache program; Rust clone/ownership, transaction codec, callback/index write semantics, runtime fault reachability and Host durable finalization remain interfaces. No semantic correspondence follows from SHA identity.',
}
mapping_file = ROOT / 'source-mapping.json'
mapping_file.write_bytes((json.dumps(mapping, indent=2, sort_keys=True) + '\n').encode())
plan = json.loads((PRIOR / 'plan.json').read_bytes())
plan['external_floor'] = {'admission_ready': True, **pin(DIAG / 'transfer-deferred-queue-external-floor-20261010-01/external-floor.json')}

plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [pin(destination)]
plan['lean_path'] = [str(POOL / 'modules'), str(ROOT / 'project')] + plan['lean_path'][2:]
plan['targets'] = [{'module': 'TransferDeferredQueueSourceModel01', 'source': pin(target),
    'predecessor_source': pin(handwritten), 'imports': ['ShielddSecurity.TransferStateDelta'], 'audit_names': new_names}]
baseline = json.loads(Path(plan['preservation']['path']).read_bytes())
plan['pins'] = inputs + [pin(p) for p in [Path(__file__), runner, handwritten, target, composition_file, mapping_file]]
plan['pins'] += mapping['runtime_sources'] + baseline['protected'] + baseline['foreign']
plan['pins'] += [plan['lean'], plan['external_floor'], plan['preservation'], pin(destination)]
plan['pins'] += [pin(DIAG / 'transfer-external-floor-complete-20261010-10/external-floor.json')]
plan['pins'] += [pin(DIAG / 'transfer-deferred-queue-model-20261010-02' / n) for n in ['plan.json', 'events.jsonl', 'handwritten/TransferDeferredQueueSourceModel01.lean', 'project/ShielddSecurity/TransferDeferredQueueSourceModel01.lean', 'runs/01-TransferDeferredQueueSourceModel01/stdout.txt']]

plan['pins'] += [pin(ROOT / 'prepare_successor.py')]
plan['pins'] += [pin(DIAG / 'transfer-deferred-queue-model-20261010-01' / n) for n in ['plan.json', 'events.jsonl', 'handwritten/TransferDeferredQueueSourceModel01.lean', 'project/ShielddSecurity/TransferDeferredQueueSourceModel01.lean', 'runs/01-TransferDeferredQueueSourceModel01/stdout.txt']]
unique = {}
for record in plan['pins']:
    assert record['path'] not in unique or unique[record['path']] == record
    unique[record['path']] = record
plan['pins'] = list(unique.values())
for k in ['deferred', 'future_queue', 'retained_failed_doubling_history', 'retained_failed_history', 'retained_failed_no16_history', 'retained_failed_witness_history']:
    plan[k] = []
plan['predecessor'] = {'state_delta_reports': pin(OLD / 'audit.json'), 'runner_plan_template': pin(PRIOR / 'plan.json')}
plan['kind'] = 'NARROW_DEFERRED_QUEUE_SOURCE_ORDER_MODEL_QUALIFICATION'
plan['scope'] = mapping['scope'] + ' Seventeen new public declaration audits; no native/control/full Transfer certification credit.'
plan['source_repairs'] = 'Fresh post-take dispatch lemma exposes the Option height match before rewriting index outcomes. Same flush definitions and existing theorem premises/conclusions; one new reusable lemma. Both rejected predecessors retained at zero credit. Exact reachable core external subclosure; physical/lint guards unchanged.'
plan['artifact_policy'] = 'One new source and bounded receipts/objects. One exact 635520-byte retained core model object copied into a separately charged complete first package root.'
plan['repairs'] = 'Minimal complete owned first package root for the actual one-module owned closure; all existing memory/time/thread/process/heartbeat/recursion/audit/byte guards unchanged.'
plan['invocation'] = 'Autonomous self-reviewed narrow model proof after the native lane admission failure; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'SOURCE_AND_PHYSICAL_GUARDS_SELF_REVIEWED_UNRUN', 'plan': pin(plan_file),
    'runner': pin(runner), 'owned_floor': pin(composition_file), 'owned_objects': 1,
    'fresh_audits': 17, 'inherited_audits': 12, 'native_credit': 0, 'certification': False,
    'scope': plan['scope']}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
