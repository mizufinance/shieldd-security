"""Qualify one failure-aware cache-program module over the accepted cache model."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
MAIN = DIAG.parent.parent
PRIOR = DIAG / 'transfer-deferred-queue-model-20261010-03'
def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
assert not (ROOT / 'plan.json').exists()
runner = ROOT / 'execute_bounded.py'
assert pin(PRIOR / runner.name)['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(PRIOR / runner.name, runner)
spec = importlib.util.spec_from_file_location('raw_program_exact_auditor', runner)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((PRIOR / 'plan.json').read_bytes())
composition = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert composition['admission_ready'] and composition['objects'] == 1 and composition['kernel_credit'] == 0
assert pin(plan['owned_import_pool']['path']) == plan['owned_import_pool']
assert len(composition['inherited_public_reports']) == 12
for selected in composition['selected']:
    assert selected['module'] == 'TransferStateDelta'
    assert all(pin(selected[k]['path']) == selected[k] for k in ['source', 'object', 'copy'])
handwritten = ROOT / 'handwritten/TransferRawStateProgram01.lean'
text = handwritten.read_text()
names = re.findall(r'^(?:structure|abbrev|def|theorem) ([A-Za-z0-9_]+)', text, re.M)
assert len(names) == 16
assert re.findall(r'^#check @([^\n]+)', text, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', text, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(text))
target = ROOT / 'project/ShielddSecurity' / handwritten.name
target.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target)
runtime = Path('C:/src/shieldd-pr160-844389ee')
sources = [pin(runtime / p) for p in ['crates/core/app/src/app/mod.rs',
    'crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
    'crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs']]
mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a', 'runtime_sources': sources,
    'raw': 'transfer_execute_validated checks the exact extracted item, executes proof-bound spend/note effects, then handles Ordinary volume. execute_proof_bound_effects obtains the source, nullifies the entire input batch, records spend events, and sequentially adds each output note/event. Rust question-mark propagation does not itself rewind earlier writes. A failing callback may also return after child-cache mutation; the model retains that failure cache.',
    'outer': 'The delivery adapter projects only successful raw outcomes to a cache. Error projection suppresses index preparation, parent apply and deferred append in the accepted TransferStateDelta run/finish program. The theorem derives parent/queue preservation without requiring a raw child-rollback or desired-parent equality premise.',
    'prefix': 'For arbitrary successful prefixes, a later error suppresses all suffix callbacks and retains the exact failing callback cache. When a rejecting callback itself preserves the incoming cache, the successful prefix cache survives the raw error. These callback-result premises are explicit primitive program facts, not opaque desired poststate laws.',
    'existing_runtime_evidence': pin(DIAG / 'transfer-runtime-completion-packet-20261010-01/manifest.json'),
    'runtime_scope': 'Previously accepted genuine after-routing/after-index delivery failures exercise enclosing child discard. The additional compiled delayed Ordinary-token raw-volume rejection and genuine Host queue controls remain unexecuted; no native result or negative-control credit is added here.',
    'scope': 'Generic failure-aware functional child-cache sequence and delivery composition only. Rust source/field projection, mutable aliases/Clone/COW, primitive storage/error behavior, native proof/capability/codec correctness, current-source changes, and Host durability remain separate correspondence interfaces. No source hash establishes semantic refinement or full Transfer certification.'}
mapping_file = ROOT / 'source-mapping.json'
mapping_file.write_bytes((json.dumps(mapping, indent=2, sort_keys=True) + '\n').encode())
plan['lean_path'][1] = str(ROOT / 'project')
plan['targets'] = [{'module': 'TransferRawStateProgram01', 'source': pin(target),
    'predecessor_source': pin(handwritten), 'imports': ['ShielddSecurity.TransferStateDelta'],
    'audit_names': ['ShielddSecurity.TransferRawStateProgram01.' + name for name in names]}]
baseline = json.loads(Path(plan['preservation']['path']).read_bytes())
plan['pins'] = baseline['protected'] + baseline['foreign'] + sources
plan['pins'] += composition['input_records']
plan['pins'] += [pin(p) for p in [Path(__file__), runner, handwritten, target, mapping_file, PRIOR / 'plan.json']]
plan['pins'] += [plan['lean'], plan['external_floor'], plan['preservation'], plan['owned_import_pool']]
plan['pins'] += plan['owned_imports'] + [mapping['existing_runtime_evidence']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())

plan['pins'] += [pin(ROOT.parent / 'transfer-raw-state-program-20261011-01' / name) for name in [
    'prepare.py', 'plan.json', 'events.jsonl', 'handwritten/TransferRawStateProgram01.lean',
    'project/ShielddSecurity/TransferRawStateProgram01.lean', 'runs/01-TransferRawStateProgram01/stdout.txt']]
plan['pins'] += [pin(ROOT / 'prepare_successor.py')]

for name in ['deferred', 'future_queue', 'retained_failed_doubling_history', 'retained_failed_history',
    'retained_failed_no16_history', 'retained_failed_witness_history']:
    plan[name] = []
plan['predecessor'] = {'accepted_core_model_composition': plan['owned_import_pool'], 'runner_plan_template': pin(PRIOR / 'plan.json')}
plan['kind'] = 'NARROW_FAILURE_AWARE_RAW_CHILD_CACHE_PROGRAM_AND_DELIVERY_MODEL'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh alpha-renaming of reserved prefix/partial binders and constructor-like unit binder, plus one proof-call arity correction. Same model definitions and theorem premises/conclusions. First rejected attempt retained at zero proof/control credit.'
plan['artifact_policy'] = 'One new handwritten source and bounded receipts/object; reuse the exact complete one-module accepted owned package root and complete Lean/Init core external closure.'
plan['repairs'] = 'None. All physical/process/thread/time/heartbeat/byte/lint/audit protections unchanged.'
plan['invocation'] = 'Autonomous self-reviewed serial narrow model proof during unmet native physical admission; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'SOURCE_AND_UNCHANGED_PHYSICAL_GUARDS_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'fresh_public_audits': 16,
    'inherited_cache_model_audits': 12, 'native_test_credit': 0, 'certification': False, 'scope': mapping['scope']}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
