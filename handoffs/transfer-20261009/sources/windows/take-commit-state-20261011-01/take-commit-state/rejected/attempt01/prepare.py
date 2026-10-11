"""Prepare overlay-derived current volume refusal on the complete qualified closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
UPSTREAM = DIAG / 'transfer-captured-recovery-20261011-04'
POOL = DIAG / 'transfer-take-commit-state-owned-floor-20261011-01'
MODULE = 'TransferTakeCommitState01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

assert not (ROOT / 'plan.json').exists() and not POOL.exists()
runner = ROOT / 'execute_bounded.py'
assert pin(UPSTREAM / runner.name)['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(UPSTREAM / runner.name, runner)
spec = importlib.util.spec_from_file_location('current_volume_complete_auditor', runner)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((UPSTREAM / 'plan.json').read_bytes())
old_pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
records = [(r['module'], r['source'], r['object']) for r in old_pool['selected']]
inputs = old_pool['input_records'][:]
audits = dict(old_pool['inherited_public_reports'])
events = [json.loads(s) for s in (UPSTREAM / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
target = plan['targets'][0]
stdout = UPSTREAM / 'runs/01-TransferCapturedRecovery01/stdout.txt'
current = m.audit(stdout.read_text(), target['audit_names'])
assert len(current) == 8 and current == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
assert set(audits).isdisjoint(current)
audits.update(current)
records.append(('TransferCapturedRecovery01', target['source'], events[-1]['result']['objects'][0]))
inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferCapturedRecovery01.lean', 'project/ShielddSecurity/TransferCapturedRecovery01.lean']]
inputs.append(pin(stdout))
assert len(records) == 63 and len(audits) == 630
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
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 63, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete sixty-three-module first owned root; 630 inherited full reports; shared StateDelta/Readback and original BankRecovery10 included exactly once. Exact qualified source/object closure and complete reports reused without replay. Exact copied objects add no new replay or Rust refinement.'}
composition_file = POOL / 'composition-review.json'
dump(composition_file, composition)
handwritten = ROOT / 'handwritten' / (MODULE + '.lean')
source = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 11 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', source, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(source))
target_source = ROOT / 'project/ShielddSecurity' / handwritten.name
target_source.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target_source)
runtime = Path('C:/src/shieldd-pr160-844389ee')
prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())
runtime_rows = {row['path']: row for row in prior_mapping['runtime_sources']}
for relative in ['crates/core/app/src/app/host.rs', 'crates/core/app/src/app/lifecycle.rs', 'crates/core/app/src/app/permanent_writer.rs', 'crates/core/component/sct/src/permanent_nullifiers/store.rs', 'crates/core/component/sct/src/permanent_nullifiers.rs']:
    row = pin(runtime / relative)
    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
    runtime_rows[row['path']] = row
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),
    'interfaces': prior_mapping['interfaces'] + ['Source state transfer uses existing actual ensureSealed model and concrete deferred index flush. Exclusive unwrap branch is actual independently observed returned native ownership result; source model returns exact previous value and restores it on failure, requiring native Arc/Clone/alias/snapshot/object getter semantic correspondence. Replacement snapshot is observed after flush, installs typed reader and empty other disposable objects. Typed key is supplied explicitly; source literal reader key, object any/downcast panics and complete finite library representation remain native interfaces. Concrete flush-derived object/V frames bind pending data without callback desired-poststate premise.'],
    'scope': 'Source App::take_commit_state uses actual ensureSealed then concrete deferred flush then fresh latest snapshot replacement containing only the current typed reader, followed by independently observed exclusive Arc unwrap success. Success transfers exact post-flush old state; failed unwrap restores that post-flush state/current queue, not pre-flush state. Concrete index failure preserves already delivered parent effects and consumes queued records while refusing transfer. Successful nonempty concrete flush preserves original V/objects, hence pending data, with actual count observation premise. Eleven reports (five data/program definitions, six proofs). Native Arc/try_unwrap exact value/reference/Clone/panic/ownership and snapshot/object key/reader/current view source correspondence remain explicit; no actual native ownership or no-hidden-alias theorem claimed. No native/control/durability/full certification and no semantic-control credit for formal refusals.'}
mapping_file = ROOT / 'source-mapping.json'
dump(mapping_file, mapping)
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': MODULE, 'source': pin(target_source), 'predecessor_source': pin(handwritten),
    'imports': ['ShielddSecurity.TransferCapturedRecovery01'],
    'audit_names': ['ShielddSecurity.' + MODULE + '.' + n for n in names]}]
baseline = json.loads(Path(plan['preservation']['path']).read_bytes())
plan['pins'] = baseline['protected'] + baseline['foreign'] + inputs + plan['owned_imports']
plan['pins'] += [pin(p) for p in [Path(__file__), ROOT / 'prepare_recipe.py', runner, handwritten, target_source, composition_file, mapping_file]]
rejected = DIAG / 'transfer-fee-funding-delivery-20261011-01'
plan['pins'] += [pin(rejected / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferFeeFundingDelivery01.lean',
    'project/ShielddSecurity/TransferFeeFundingDelivery01.lean', 'runs/01-TransferFeeFundingDelivery01/stdout.txt']]
rejected_second = DIAG / 'transfer-fee-funding-delivery-20261011-02'
plan['pins'] += [pin(rejected_second / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferFeeFundingDelivery01.lean',
    'project/ShielddSecurity/TransferFeeFundingDelivery01.lean', 'runs/01-TransferFeeFundingDelivery01/stdout.txt']]
rejected_body = DIAG / 'transfer-deferred-body-failure-20261011-01'
plan['pins'] += [pin(rejected_body / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferDeferredBodyFailure01.lean',
    'project/ShielddSecurity/TransferDeferredBodyFailure01.lean', 'runs/01-TransferDeferredBodyFailure01/stdout.txt']]
withdrawn_setup = DIAG / 'transfer-deferred-body-failure-20261011-02'
plan['pins'] += [pin(withdrawn_setup / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'handwritten/TransferDeferredBodyFailure01.lean', 'project/ShielddSecurity/TransferDeferredBodyFailure01.lean']]
plan['pins'].append(pin(DIAG / 'transfer-pending-nullifier-retention-20261011-01/prepare-rejected-source-association.py'))
rejected_retention = DIAG / 'transfer-pending-nullifier-retention-20261011-01'
plan['pins'] += [pin(rejected_retention / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferPendingNullifierRetention01.lean',
    'project/ShielddSecurity/TransferPendingNullifierRetention01.lean', 'runs/01-TransferPendingNullifierRetention01/stdout.txt']]
stopped_prepare = DIAG / 'transfer-pending-set-invariant-20261011-01'
plan['pins'] += [pin(stopped_prepare / n) for n in ['prepare_recipe.py', 'prepare.py', 'handwritten/TransferPendingSetInvariant01.lean', 'project/ShielddSecurity/TransferPendingSetInvariant01.lean']]
plan['pins'].append(pin(DIAG / 'transfer-pending-set-invariant-owned-floor-20261011-01/composition-review.json'))
rejected_seal = DIAG / 'transfer-pending-seal-source-20261011-01'
plan['pins'] += [pin(rejected_seal / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferPendingSealSource01.lean',
    'project/ShielddSecurity/TransferPendingSealSource01.lean', 'runs/01-TransferPendingSealSource01/stdout.txt']]
rejected_seal_second = DIAG / 'transfer-pending-seal-source-20261011-02'
plan['pins'] += [pin(rejected_seal_second / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferPendingSealSource01.lean',
    'project/ShielddSecurity/TransferPendingSealSource01.lean', 'runs/01-TransferPendingSealSource01/stdout.txt']]
rejected_stateful = DIAG / 'transfer-stateful-store-commit-20261011-01'
plan['pins'] += [pin(rejected_stateful / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferStatefulStoreCommit01.lean', 'project/ShielddSecurity/TransferStatefulStoreCommit01.lean', 'runs/01-TransferStatefulStoreCommit01/stdout.txt']]
rejected_captured = DIAG / 'transfer-captured-recovery-20261011-01'
plan['pins'] += [pin(rejected_captured / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferCapturedRecovery01.lean', 'project/ShielddSecurity/TransferCapturedRecovery01.lean', 'runs/01-TransferCapturedRecovery01/stdout.txt']]
unrun_captured = DIAG / 'transfer-captured-recovery-20261011-02'
assert not (unrun_captured/'events.jsonl').exists()
plan['pins'] += [pin(unrun_captured / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'handwritten/TransferCapturedRecovery01.lean', 'project/ShielddSecurity/TransferCapturedRecovery01.lean']]
rejected_captured03 = DIAG / 'transfer-captured-recovery-20261011-03'
plan['pins'] += [pin(rejected_captured03 / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferCapturedRecovery01.lean', 'project/ShielddSecurity/TransferCapturedRecovery01.lean', 'runs/01-TransferCapturedRecovery01/stdout.txt']]

plan['pins'].append(pin(UPSTREAM / 'rejected-object-identity.json'))
plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'SOURCE_TAKE_COMMIT_STATE_SEALED_CONCRETE_FLUSH_EXCLUSIVE_TRANSFER_AND_REPLACEMENT'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh handwritten actual source transfer with concrete reused flush proofs. Native ownership/library semantic contracts remain interfaces; no ancestor replay or native/control/certification credit. Guards unchanged.'
plan['artifact_policy'] = 'One source and bounded reports/object; complete sixty-three-module owned root and reachable core floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit guards unchanged.'
plan['invocation'] = 'Autonomous serial narrow source writer preparation proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'TAKE_COMMIT_STATE_COMPLETE_SIXTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 11, 'inherited_audits': 630, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
dump(ROOT / 'review.json', review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
