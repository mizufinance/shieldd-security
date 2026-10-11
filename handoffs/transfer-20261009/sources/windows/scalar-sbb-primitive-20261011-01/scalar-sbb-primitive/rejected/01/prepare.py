"""Prepare overlay-derived current volume refusal on the complete qualified closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
UPSTREAM = DIAG / 'transfer-scalar-adc-shift-20261011-02'
POOL = DIAG / 'transfer-scalar-sbb-primitive-owned-floor-20261011-01'
MODULE = 'TransferScalarSbbPrimitive01'

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
stdout = UPSTREAM / 'runs/01-TransferScalarAdcShift01/stdout.txt'
current = m.audit(stdout.read_text(), target['audit_names'])
assert len(current) == 8 and current == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
assert set(audits).isdisjoint(current)
audits.update(current)
records.append(('TransferScalarAdcShift01', target['source'], events[-1]['result']['objects'][0]))
inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferScalarAdcShift01.lean', 'project/ShielddSecurity/TransferScalarAdcShift01.lean']]
inputs.append(pin(stdout))
assert len(records) == 83 and len(audits) == 785
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
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 83, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete eighty-three-module first owned root; 785 inherited full reports; shared StateDelta/Readback and original BankRecovery10 included exactly once. Exact qualified source/object closure and complete reports reused without replay. Exact copied objects add no new replay or Rust refinement.'}
composition_file = POOL / 'composition-review.json'
dump(composition_file, composition)
handwritten = ROOT / 'handwritten' / (MODULE + '.lean')
source = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 9 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', source, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(source))
target_source = ROOT / 'project/ShielddSecurity' / handwritten.name
target_source.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target_source)
runtime = Path('C:/src/shieldd-pr160-844389ee')
prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())
runtime_rows = {row['path']: row for row in prior_mapping['runtime_sources']}
for relative in ['crates/core/component/sct/src/component/sct.rs', 'crates/core/app/src/app/host.rs', 'crates/core/app/src/app/lifecycle.rs', 'crates/core/app/src/app/permanent_writer.rs', 'crates/core/component/sct/src/permanent_nullifiers/store.rs', 'crates/core/component/sct/src/permanent_nullifiers.rs']:
    row = pin(runtime / relative)
    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
    runtime_rows[row['path']] = row
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),
    'interfaces': prior_mapping['interfaces'] + ['Source-shaped reachable-borrow-mask SBB widens finite UInt64 operands, extracts incoming mask high bit, uses BitVec128 wrapping subtraction and exact fixed shift/casts. Small lemmas prove full wrapping integer normal form, underflow/nonunderflow values, exact zero/all-ones outgoing borrow mask and low-word subtraction conservation. Nine full reports: four definitions/five theorems. Only single-word constant-width linear arithmetic, no wide constraint walk. Actual Rust primitive/trace/whole subtraction and add-back/endian semantics remain interfaces. Zero native/control/certification credit.'], 'scope': 'Source-shaped reachable-borrow-mask SBB widens finite UInt64 operands, extracts incoming mask high bit, uses BitVec128 wrapping subtraction and exact fixed shift/casts. Small lemmas prove full wrapping integer normal form, underflow/nonunderflow values, exact zero/all-ones outgoing borrow mask and low-word subtraction conservation. Nine full reports: four definitions/five theorems. Only single-word constant-width linear arithmetic, no wide constraint walk. Actual Rust primitive/trace/whole subtraction and add-back/endian semantics remain interfaces. Zero native/control/certification credit.'}
domain = json.loads((DIAG/'transfer-bounded-native-codec-20261011-02/context/canonical-domain.json').read_bytes())
for row in domain['runtime_sources']:
    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
    runtime_rows[row['path']] = row
mapping['runtime_sources'] = list(runtime_rows.values())
mapping['canonical_nullifier_domain'] = domain
mapping['library_sources'] = domain['library_sources']
wordContext = [pin(DIAG/'transfer-scalar-word-primitives-20261011-02/capture_source.py')] + [pin(p) for p in sorted((DIAG/'transfer-scalar-word-primitives-20261011-02/context').iterdir()) if p.is_file()]
mapping['word_primitive_context'] = wordContext
mapping['serializer_wrapper_source_association'] = pin(DIAG/'transfer-scalar-four-round-wrapper-20261011-02/context/source-association.json')

mapping_file = ROOT / 'source-mapping.json'
dump(mapping_file, mapping)
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': MODULE, 'source': pin(target_source), 'predecessor_source': pin(handwritten),
    'imports': ['ShielddSecurity.TransferScalarAdcShift01'],
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

plan['pins'].append(pin(DIAG / 'transfer-take-commit-state-20261011-02/rejected-object-identity.json'))
rejected_take = DIAG / 'transfer-take-commit-state-20261011-01'
plan['pins'] += [pin(rejected_take / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferTakeCommitState01.lean', 'project/ShielddSecurity/TransferTakeCommitState01.lean', 'runs/01-TransferTakeCommitState01/stdout.txt']]

rejected_host = DIAG / 'transfer-host-sealed-commit-20261011-01'
plan['pins'] += [pin(rejected_host / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferHostSealedCommit01.lean', 'project/ShielddSecurity/TransferHostSealedCommit01.lean', 'runs/01-TransferHostSealedCommit01/stdout.txt']]
rejected_host02 = DIAG / 'transfer-host-sealed-commit-20261011-02'
plan['pins'] += [pin(rejected_host02 / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferHostSealedCommit01.lean', 'project/ShielddSecurity/TransferHostSealedCommit01.lean', 'runs/01-TransferHostSealedCommit01/stdout.txt']]
rejected_host03 = DIAG / 'transfer-host-sealed-commit-20261011-03'
plan['pins'] += [pin(rejected_host03 / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferHostSealedCommit01.lean', 'project/ShielddSecurity/TransferHostSealedCommit01.lean', 'runs/01-TransferHostSealedCommit01/stdout.txt']]
plan['pins'].append(pin(DIAG / 'transfer-capstone-plan-20261011-01/plan.json'))
rejected_host_seal = DIAG / 'transfer-host-seal-20261011-01'
plan['pins'] += [pin(rejected_host_seal / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferHostSeal01.lean', 'project/ShielddSecurity/TransferHostSeal01.lean', 'runs/01-TransferHostSeal01/stdout.txt']]
rejected_current = DIAG / 'transfer-writer-recover-current-20261011-01'
plan['pins'] += [pin(rejected_current / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferWriterRecoverCurrent01.lean', 'project/ShielddSecurity/TransferWriterRecoverCurrent01.lean', 'runs/01-TransferWriterRecoverCurrent01/stdout.txt']]
rejected_pipeline = DIAG / 'transfer-end-to-end-20261011-01'
plan['pins'] += [pin(rejected_pipeline / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferEndToEnd01.lean', 'project/ShielddSecurity/TransferEndToEnd01.lean', 'runs/01-TransferEndToEnd01/stdout.txt']]
plan['pins'].append(pin(DIAG/'transfer-bounded-native-codec-20261011-02/prepare_recipe_count_failure.py'))
superseded_byte_only = DIAG/'transfer-bounded-native-codec-20261011-01'
plan['pins'] += [pin(superseded_byte_only/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferBoundedNativeCodec01.lean','project/ShielddSecurity/TransferBoundedNativeCodec01.lean','runs/01-TransferBoundedNativeCodec01/stdout.txt']]
plan['pins'] += [pin(DIAG/'transfer-bounded-native-codec-20261011-02/context/canonical-domain.json')] + domain['library_sources'] + [domain['math_source']]
unrun_ghost_wide = DIAG/'transfer-native-seal-transfer-20261011-01'
assert not (unrun_ghost_wide/'events.jsonl').exists()
plan['pins'] += [pin(unrun_ghost_wide/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferNativeSealTransfer01.lean','project/ShielddSecurity/TransferNativeSealTransfer01.lean']]
rejected_native_seal = DIAG/'transfer-native-seal-transfer-20261011-02'
plan['pins'] += [pin(rejected_native_seal/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeSealTransfer01.lean','project/ShielddSecurity/TransferNativeSealTransfer01.lean','runs/01-TransferNativeSealTransfer01/stdout.txt']]
rejected_native_raw=DIAG/'transfer-native-raw-pending-20261011-01'
plan['pins'] += [pin(rejected_native_raw/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeRawPending01.lean','project/ShielddSecurity/TransferNativeRawPending01.lean','runs/01-TransferNativeRawPending01/stdout.txt']]
rejected_native_raw02=DIAG/'transfer-native-raw-pending-20261011-02'
plan['pins'] += [pin(rejected_native_raw02/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeRawPending01.lean','project/ShielddSecurity/TransferNativeRawPending01.lean','runs/01-TransferNativeRawPending01/stdout.txt']]
rejected_erasure=DIAG/'transfer-native-ghost-erasure-20261011-01'
plan['pins'] += [pin(rejected_erasure/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeGhostErasure01.lean','project/ShielddSecurity/TransferNativeGhostErasure01.lean','runs/01-TransferNativeGhostErasure01/stdout.txt']]
rejected_reachable=DIAG/'transfer-native-reachable-erasure-20261011-01'
plan['pins'] += [pin(rejected_reachable/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeReachableErasure01.lean','project/ShielddSecurity/TransferNativeReachableErasure01.lean','runs/01-TransferNativeReachableErasure01/stdout.txt']]
rejected_reachable02=DIAG/'transfer-native-reachable-erasure-20261011-02'
plan['pins'] += [pin(rejected_reachable02/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeReachableErasure01.lean','project/ShielddSecurity/TransferNativeReachableErasure01.lean','runs/01-TransferNativeReachableErasure01/stdout.txt']]
plan['pins'] += wordContext + [mapping['serializer_wrapper_source_association']]
plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]
failed_scalar = DIAG / 'transfer-scalar-serialization-range-20261011-01'
plan['pins'] += [pin(failed_scalar/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarSerializationRange01.lean','project/ShielddSecurity/TransferScalarSerializationRange01.lean','runs/01-TransferScalarSerializationRange01/stdout.txt']]
unrunWords = DIAG/'transfer-scalar-word-primitives-20261011-01'
plan['pins'] += [pin(unrunWords/n) for n in ['capture_source.py','prepare_recipe.py','prepare.py','handwritten/TransferScalarWordPrimitives01.lean']]
failedWords = DIAG/'transfer-scalar-word-primitives-20261011-02'
plan['pins'] += [pin(failedWords/n) for n in ['capture_source.py','prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarWordPrimitives01.lean','project/ShielddSecurity/TransferScalarWordPrimitives01.lean','runs/01-TransferScalarWordPrimitives01/stdout.txt']]
failedCarry = DIAG/'transfer-scalar-carry-schedule-20261011-01'
plan['pins'] += [pin(failedCarry/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCarrySchedule01.lean','project/ShielddSecurity/TransferScalarCarrySchedule01.lean','runs/01-TransferScalarCarrySchedule01/stdout.txt']]
failedWrapper = DIAG/'transfer-scalar-four-round-wrapper-20261011-01'
plan['pins'] += [pin(failedWrapper/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/source-association.json','handwritten/TransferScalarFourRoundWrapper01.lean','project/ShielddSecurity/TransferScalarFourRoundWrapper01.lean','runs/01-TransferScalarFourRoundWrapper01/stdout.txt']]
failedAdc = DIAG/'transfer-scalar-adc-shift-20261011-01'
plan['pins'] += [pin(failedAdc/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarAdcShift01.lean','project/ShielddSecurity/TransferScalarAdcShift01.lean','runs/01-TransferScalarAdcShift01/stdout.txt']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'SOURCE_SCALAR_REACHABLE_BORROW_MASK_SBB_SINGLE_WORD_ARITHMETIC'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh reachable-mask single-word SBB arithmetic refinement on complete 785-report/83-module ancestry. Small finite-width lemmas, exact preserved source and diagnostics, no replay or guard changes.'
plan['artifact_policy'] = 'One source and bounded reports/object; complete eighty-three-module owned root and reachable core floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit guards unchanged.'
plan['invocation'] = 'Autonomous serial narrow source writer preparation proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'SCALAR_SBB_PRIMITIVE_COMPLETE_EIGHTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 9, 'inherited_audits': 785, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
dump(ROOT / 'review.json', review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
