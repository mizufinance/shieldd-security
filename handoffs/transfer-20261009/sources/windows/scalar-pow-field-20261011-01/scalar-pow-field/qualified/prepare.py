"""Prepare overlay-derived current volume refusal on the complete qualified closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
UPSTREAM = DIAG / 'transfer-scalar-pow-bit-integer-20261012-03'
POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-08'
MODULE = 'TransferScalarPowField01'

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
stdout = UPSTREAM / 'runs/01-TransferScalarPowBitInteger01/stdout.txt'
current = m.audit(stdout.read_text(), target['audit_names'])
assert len(current)==6 and current==events[-1]['result']['audits']
assert pin(stdout)==events[-1]['result']['stdout'] and set(audits).isdisjoint(current)
audits.update(current)
records.append(('TransferScalarPowBitInteger01',target['source'],events[-1]['result']['objects'][0]))
inputs += [pin(UPSTREAM/n) for n in ['prepare_recipe.py','prepare.py','plan.json','events.jsonl','execute_bounded.py','source-mapping.json','handwritten/TransferScalarPowBitInteger01.lean','project/ShielddSecurity/TransferScalarPowBitInteger01.lean']]+[pin(stdout)]
assert len(records)==163 and len(audits)==1296
bits=UPSTREAM

originalInputs=inputs[:]
inputs=list({json.dumps(row,sort_keys=True,separators=(',',':')):row for row in inputs}.values())
assert {json.dumps(row,sort_keys=True,separators=(',',':')) for row in originalInputs}=={json.dumps(row,sort_keys=True,separators=(',',':')) for row in inputs}

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
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 163, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete one-hundred-sixty-one-module first owned root; 1283 inherited full reports; shared StateDelta/Readback and original BankRecovery10 included exactly once. Exact qualified source/object closure and complete reports reused without replay. Exact copied objects add no new replay or Rust refinement.'}
composition['scope']='Complete163-module first owned root and1296 complete original reports: exact qualified whole bit-integer/word branch reused without replay. The independently qualified inverse/prime branch remains a separate original packet; no unsupported external imports selected.'
composition_file = POOL / 'composition-review.json'
dump(composition_file, composition)
handwritten = ROOT / 'handwritten' / (MODULE + '.lean')
source = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 6 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
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
for row in json.loads((DIAG/'transfer-checked-word-fresh-snapshot-20261011-01/context/source-fresh-snapshot-shape.json').read_bytes())['runtime_sources']:
    assert row['path'] not in runtime_rows or runtime_rows[row['path']]==row
    runtime_rows[row['path']]=row
mapping = dict(prior_mapping)
mapping['interfaces'] = prior_mapping['interfaces'] + ['Actual modeled constant/variable square/multiply bit steps and symbolic source word folds derive exact mathematical field powers for complete source pow/pow_vartime, using derived source ONE initial value and exact reconstructed little-endian exponent integer. Six theorem audits. Whole203-module inverse/prime branch and whole163-module bit branch merged with exact shared162-module source/object/report identity; no ancestor replay. Native Choice/library/compiler/ABI/caller/full Transfer remain open.']
mapping['scope'] = 'Actual modeled constant/variable bit/word folds derive complete source pow mathematical field values from exact ONE and little-endian exponent reconstruction. Six theorem audits. Complete163-module1296-report qualified word branch reused unchanged without replay. Independently qualified inverse/prime branch preserved as its separate original packet; native Choice/compiler/caller/full Transfer remain open.'
mapping['sct_pending_read_source_shape']=pin(DIAG/'transfer-word-sct-pending-read-20261011-01/context/sct-pending-read-shape.json')
mapping['checked_pending_put_source_shape']=pin(DIAG/'transfer-word-object-put-20261011-03/context/checked-pending-put-shape.json')
mapping['saturating_capacity_source_shape']=pin(DIAG/'transfer-pending-saturating-capacity-20261011-01/context/saturating-capacity-shape.json')
mapping['checked_pending_read_source_shape'] = pin(DIAG/'transfer-word-object-read-20261011-03/context/checked-pending-read-shape.json')

mapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')
mapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')
mapping['wide_reduction_source_shape']=pin(DIAG/'transfer-scalar-wide-round-20261011-04/context/wide-reduction-shape.json')
mapping['r2_decoder_payload_source_shape']=pin(DIAG/'transfer-scalar-r2-payload-20261011-01/context/r2-decoder-payload-shape.json')
mapping['corrected_finalization_source_order']=pin(DIAG/'transfer-source-ordered-finalizer-20261011-03/context/corrected-finalization-call-order.json')

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
mapping['serializer_byte_source_association'] = pin(DIAG/'transfer-scalar-little-endian-bytes-20261011-02/context/serializer-byte-shape.json')

mapping['action_projection_source_association'] = pin(DIAG/'transfer-source-typed-input-projection-20261011-03/context/source-projection-shape.json')
projectionAssociation = json.loads(Path(mapping['action_projection_source_association']['path']).read_bytes())
for row in projectionAssociation['runtime_sources']:
    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
    runtime_rows[row['path']] = row
mapping['runtime_sources'] = list(runtime_rows.values())
mapping['known_finalization_source_association'] = pin(DIAG/'transfer-finalization-object-frames-20261011-01/context/known-finalization-object-mutators.json')
finalizationAssociation = json.loads(Path(mapping['known_finalization_source_association']['path']).read_bytes())
for row in finalizationAssociation['runtime_sources']:
    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
    runtime_rows[row['path']] = row
mapping['runtime_sources'] = list(runtime_rows.values())
mapping['fixed_finalization_source_association'] = pin(DIAG/'transfer-fixed-finalizer-publication-20261011-01/context/fixed-finalization-call-shape.json')
mapping['checked_word_seal_source_shape']=pin(DIAG/'transfer-checked-word-seal-20261011-03/context/checked-word-seal-shape.json')
mapping['fresh_snapshot_source_shape']=pin(DIAG/'transfer-checked-word-fresh-snapshot-20261011-01/context/source-fresh-snapshot-shape.json')
mapping['checked_word_accepted_source_shape']=pin(DIAG/'transfer-checked-word-accepted-input-20261011-02/context/checked-word-accepted-source-shape.json')
mapping['scalar_canonical_add_source_shape']=pin(DIAG/'transfer-scalar-canonical-add-20261011-02/context/scalar-canonical-add-shape.json')
mapping['scalar_canonical_sub_source_shape']=pin(DIAG/'transfer-scalar-canonical-sub-20261011-02/context/scalar-canonical-sub-shape.json')
mapping['scalar_canonical_neg_source_shape']=pin(DIAG/'transfer-scalar-canonical-neg-20261011-03/context/scalar-canonical-neg-shape.json')
mapping['scalar_program_family_source_shape']=pin(DIAG/'transfer-scalar-program-invariant-20261011-01/context/scalar-program-family-shape.json')
mapping['scalar_wide_constructor_source_shape']=pin(DIAG/'transfer-scalar-wide-constructor-20261011-03/context/scalar-wide-constructor-shape.json')
mapping['scalar_wide_byte_input_source_shape']=pin(DIAG/'transfer-scalar-wide-byte-input-20261011-02/context/scalar-wide-byte-input-shape.json')
mapping['scalar_input_family_source_shape']=pin(DIAG/'transfer-scalar-input-family-20261011-04/context/scalar-input-family-shape.json')
mapping['scalar_square_cross_source_shape']=pin(DIAG/'transfer-scalar-square-cross-20261011-02/context/scalar-square-cross-shape.json')
mapping['scalar_square_shift_source_shape']=pin(DIAG/'transfer-scalar-square-shift-20261011-04/context/scalar-square-shift-shape.json')
mapping['scalar_square_diagonal_source_shape']=pin(DIAG/'transfer-scalar-square-diagonal-20261011-04/context/scalar-square-diagonal-shape.json')
mapping['scalar_square_product_source_shape']=pin(DIAG/'transfer-scalar-square-product-20261011-02/context/scalar-square-product-shape.json')
mapping['scalar_pow_invariant_source_shape']=pin(DIAG/'transfer-scalar-pow-invariant-20261011-01/context/scalar-pow-invariant-shape.json')
mapping['scalar_invert_machine_source_shape']=pin(DIAG/'transfer-scalar-invert-machine-20261011-01/context/scalar-invert-machine-shape.json')
mapping['scalar_invert_chain_source_shape']=pin(DIAG/'transfer-scalar-invert-chain-20261011-05/context/scalar-invert-chain-shape.json')
mapping['scalar_public_constants_source_shape']=pin(DIAG/'transfer-scalar-public-constants-20261011-02/context/scalar-public-constants-shape.json')
mapping['scalar_extended_family_source_shape']=pin(DIAG/'transfer-scalar-extended-family-20261012-01/context/scalar-extended-family-shape.json')
mapping['scalar_field_values_source_shape']=pin(DIAG/'transfer-scalar-field-values-20261012-01/context/scalar-field-values-shape.json')
mapping['scalar_invert_field_source_shape']=pin(DIAG/'transfer-scalar-invert-field-20261012-03/context/scalar-invert-field-shape.json')
mapping['scalar_pow_bit_integer_source_shape']=pin(bits/'context/scalar-pow-bit-integer-shape.json')
mapping['scalar_pow_field_source_shape']=pin(ROOT/'context/scalar-pow-field-shape.json')
mapping_file = ROOT / 'source-mapping.json'
dump(mapping_file, mapping)
# Exact already qualified pure Core floor and package roots inherited unchanged from the bit branch.
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': MODULE, 'source': pin(target_source), 'predecessor_source': pin(handwritten),
    'imports': ['ShielddSecurity.TransferScalarFieldValues01', 'ShielddSecurity.TransferScalarPowBitInteger01'],
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
plan['pins'] += [mapping['action_projection_source_association'],mapping['known_finalization_source_association']]
plan['pins'].append(mapping['fixed_finalization_source_association'])
plan['pins'] += wordContext + [mapping['serializer_wrapper_source_association'], mapping['serializer_byte_source_association']]
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
failedSbb = DIAG/'transfer-scalar-sbb-primitive-20261011-01'
plan['pins'] += [pin(failedSbb/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarSbbPrimitive01.lean','project/ShielddSecurity/TransferScalarSbbPrimitive01.lean','runs/01-TransferScalarSbbPrimitive01/stdout.txt']]
failedNormalization = DIAG/'transfer-scalar-masked-normalization-20261011-01'
plan['pins'] += [pin(failedNormalization/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarMaskedNormalization01.lean','project/ShielddSecurity/TransferScalarMaskedNormalization01.lean','runs/01-TransferScalarMaskedNormalization01/stdout.txt']]
failedBytes = DIAG/'transfer-scalar-little-endian-bytes-20261011-01'
plan['pins'] += [pin(failedBytes/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/serializer-byte-shape.json','handwritten/TransferScalarLittleEndianBytes01.lean','project/ShielddSecurity/TransferScalarLittleEndianBytes01.lean','runs/01-TransferScalarLittleEndianBytes01/stdout.txt']]
failedMontgomery = DIAG/'transfer-scalar-montgomery-value-20261011-01'
plan['pins'] += [pin(failedMontgomery/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarMontgomeryValue01.lean','project/ShielddSecurity/TransferScalarMontgomeryValue01.lean','runs/01-TransferScalarMontgomeryValue01/stdout.txt']]
failedMontgomery02 = DIAG/'transfer-scalar-montgomery-value-20261011-02'
plan['pins'] += [pin(failedMontgomery02/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarMontgomeryValue01.lean','project/ShielddSecurity/TransferScalarMontgomeryValue01.lean','runs/01-TransferScalarMontgomeryValue01/stdout.txt']]
pressureStopped = DIAG/'transfer-scalar-padded-carry-20261011-01'
plan['pins'] += [pin(pressureStopped/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarPaddedCarry01.lean','project/ShielddSecurity/TransferScalarPaddedCarry01.lean']]
failedPadded02 = DIAG/'transfer-scalar-padded-carry-20261011-02'
plan['pins'] += [pin(failedPadded02/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarPaddedCarry01.lean','project/ShielddSecurity/TransferScalarPaddedCarry01.lean','runs/01-TransferScalarPaddedCarry01/stdout.txt']]
failedProjection = DIAG/'transfer-source-typed-input-projection-20261011-01'
plan['pins'] += [pin(failedProjection/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/source-projection-shape.json','handwritten/TransferSourceTypedInputProjection01.lean','project/ShielddSecurity/TransferSourceTypedInputProjection01.lean','runs/01-TransferSourceTypedInputProjection01/stdout.txt']]
failedProjection02 = DIAG/'transfer-source-typed-input-projection-20261011-02'
plan['pins'] += [pin(failedProjection02/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/source-projection-shape.json','handwritten/TransferSourceTypedInputProjection01.lean','project/ShielddSecurity/TransferSourceTypedInputProjection01.lean','runs/01-TransferSourceTypedInputProjection01/stdout.txt']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'SOURCE_KNOWN_POST_SEAL_OBJECT_MUTATION_FRAMES'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Actual getter derived from returned complete fresh snapshot checked-word walk/seal determines ordered accepted source key vector, exact global Montgomery value projection, uniqueness/capacity, every canonical key bound and durable false lookup. Every original typed word field serializes to exactly32 bytes and canonical Montgomery key. One definition/three theorem audits. Host source pending getter then iter/copied/collect/prepare shape is associated statically, not native semantic credit. Native imbl/Vec/iter/copied/collect/Nullifier Copy/private Scalar/reader/ABI/compiler/Host/writer/full trace binding OPEN; all prior failure/metadata histories retained zero credit; no runtime/control/replay/certification credit.'
plan['pins'] += [mapping['corrected_finalization_source_order'], pin(DIAG/'transfer-source-ordered-finalizer-20261011-01/prepare_recipe.py')]
failedCanonical=DIAG/'transfer-canonical-word-equality-20261011-01'
plan['pins'] += [pin(failedCanonical/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalWordEquality01.lean','project/ShielddSecurity/TransferCanonicalWordEquality01.lean','runs/01-TransferCanonicalWordEquality01/stdout.txt']]
pressureOrdered=DIAG/'transfer-source-ordered-finalizer-20261011-02'
plan['pins'] += [pin(pressureOrdered/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/corrected-finalization-call-order.json','handwritten/TransferSourceOrderedFinalizer01.lean','project/ShielddSecurity/TransferSourceOrderedFinalizer01.lean','runs/01-TransferSourceOrderedFinalizer01/stdout.txt']]
failedReversed=DIAG/'transfer-scalar-reversed-byte-order-20261011-01'
plan['pins'] += [pin(failedReversed/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarReversedByteOrder01.lean','project/ShielddSecurity/TransferScalarReversedByteOrder01.lean','runs/01-TransferScalarReversedByteOrder01/stdout.txt']]
failedReversed02=DIAG/'transfer-scalar-reversed-byte-order-20261011-02'
plan['pins'] += [pin(failedReversed02/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarReversedByteOrder01.lean','project/ShielddSecurity/TransferScalarReversedByteOrder01.lean','runs/01-TransferScalarReversedByteOrder01/stdout.txt']]
failedByteKey=DIAG/'transfer-byte-key-cache-20261011-01'
plan['pins'] += [pin(failedByteKey/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferByteKeyCache01.lean','project/ShielddSecurity/TransferByteKeyCache01.lean','runs/01-TransferByteKeyCache01/stdout.txt']]
pressureByteKey=DIAG/'transfer-byte-key-cache-20261011-02'
plan['pins'] += [pin(pressureByteKey/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferByteKeyCache01.lean','project/ShielddSecurity/TransferByteKeyCache01.lean','runs/01-TransferByteKeyCache01/stdout.txt']]
unrunByteKey=DIAG/'transfer-byte-key-cache-20261011-03'
assert not (unrunByteKey/'events.jsonl').exists()
plan['pins'] += [pin(unrunByteKey/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferByteKeyCache01.lean','project/ShielddSecurity/TransferByteKeyCache01.lean']]
plan['pins'].append(mapping['scalar_decode_source_shape'])
unrunDecode=DIAG/'transfer-scalar-byte-decode-20261011-01'
assert not (unrunDecode/'events.jsonl').exists()
plan['pins'] += [pin(unrunDecode/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/decoder-shape.json','handwritten/TransferScalarByteDecode01.lean','project/ShielddSecurity/TransferScalarByteDecode01.lean']]
plan['pins'].append(mapping['wide_product_source_shape'])
plan['pins'].append(mapping['wide_reduction_source_shape'])
plan['pins'] += [pin(DIAG/'transfer-scalar-wide-round-20261011-01/prepare_recipe.py'), pin(DIAG/'transfer-scalar-wide-round-20261011-01/handwritten/TransferScalarWideRound01.lean')]
failedWide=DIAG/'transfer-scalar-wide-round-20261011-02'
plan['pins'] += [pin(failedWide/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/wide-reduction-shape.json','handwritten/TransferScalarWideRound01.lean','project/ShielddSecurity/TransferScalarWideRound01.lean','runs/01-TransferScalarWideRound01/stdout.txt']]
failedWide03=DIAG/'transfer-scalar-wide-round-20261011-03'
plan['pins'] += [pin(failedWide03/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/wide-reduction-shape.json','handwritten/TransferScalarWideRound01.lean','project/ShielddSecurity/TransferScalarWideRound01.lean','runs/01-TransferScalarWideRound01/stdout.txt']]
failedWalk=DIAG/'transfer-scalar-wide-walk-20261011-01'
plan['pins'] += [pin(failedWalk/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarWideWalk01.lean','project/ShielddSecurity/TransferScalarWideWalk01.lean','runs/01-TransferScalarWideWalk01/stdout.txt']]
failedReduction=DIAG/'transfer-scalar-wide-reduction-20261011-01'
plan['pins'] += [pin(failedReduction/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarWideReduction01.lean','project/ShielddSecurity/TransferScalarWideReduction01.lean','runs/01-TransferScalarWideReduction01/stdout.txt']]
plan['pins'].append(mapping['r2_decoder_payload_source_shape'])
failedKey=DIAG/'transfer-scalar-canonical-key-20261011-01'
plan['pins'] += [pin(failedKey/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCanonicalKey01.lean','project/ShielddSecurity/TransferScalarCanonicalKey01.lean','runs/01-TransferScalarCanonicalKey01/stdout.txt']]
failedKey02=DIAG/'transfer-scalar-canonical-key-20261011-02'
plan['pins'] += [pin(failedKey02/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCanonicalKey01.lean','project/ShielddSecurity/TransferScalarCanonicalKey01.lean','runs/01-TransferScalarCanonicalKey01/stdout.txt']]
failedWord=DIAG/'transfer-canonical-word-pending-20261011-01'
plan['pins'] += [pin(failedWord/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalWordPending01.lean','project/ShielddSecurity/TransferCanonicalWordPending01.lean','runs/01-TransferCanonicalWordPending01/stdout.txt']]
failedWord02=DIAG/'transfer-canonical-word-pending-20261011-02'
plan['pins'] += [pin(failedWord02/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalWordPending01.lean','project/ShielddSecurity/TransferCanonicalWordPending01.lean','runs/01-TransferCanonicalWordPending01/stdout.txt']]
unrunDriver = DIAG/'transfer-word-source-driver-20261011-01'
assert not (unrunDriver/'events.jsonl').exists() and not (unrunDriver/'plan.json').exists()
plan['pins'] += [pin(unrunDriver/n) for n in ['prepare_recipe.py','prepare.py','handwritten/TransferWordSourceDriver01.lean']]
pressureDriver = DIAG/'transfer-word-source-driver-20261011-02'
plan['pins'] += [pin(pressureDriver/n) for n in ['repair_recipe.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordSourceDriver01.lean','project/ShielddSecurity/TransferWordSourceDriver01.lean']]
plan['pins'].append(mapping['checked_pending_read_source_shape'])
unrunRead=DIAG/'transfer-word-object-read-20261011-01'
assert not (unrunRead/'events.jsonl').exists()
plan['pins'] += [pin(unrunRead/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferWordObjectRead01.lean','project/ShielddSecurity/TransferWordObjectRead01.lean','context/checked-pending-read-shape.json']]
pressureRead=DIAG/'transfer-word-object-read-20261011-02'
plan['pins'] += [pin(pressureRead/n) for n in ['repair_recipe.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordObjectRead01.lean','project/ShielddSecurity/TransferWordObjectRead01.lean','context/checked-pending-read-shape.json']]
plan['pins'].append(mapping['saturating_capacity_source_shape'])
pressureLayers=DIAG/'transfer-word-layered-object-read-20261011-01'
plan['pins'] += [pin(pressureLayers/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordLayeredObjectRead01.lean','project/ShielddSecurity/TransferWordLayeredObjectRead01.lean']]
failedFlat=DIAG/'transfer-word-layer-flatten-20261011-01'
plan['pins'] += [pin(failedFlat/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordLayerFlatten01.lean','project/ShielddSecurity/TransferWordLayerFlatten01.lean','runs/01-TransferWordLayerFlatten01/stdout.txt']]
pressureFlat=DIAG/'transfer-word-layer-flatten-20261011-02'
plan['pins'] += [pin(pressureFlat/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordLayerFlatten01.lean','project/ShielddSecurity/TransferWordLayerFlatten01.lean']]
plan['pins'].append(mapping['checked_pending_put_source_shape'])
failedPut=DIAG/'transfer-word-object-put-20261011-01'
plan['pins'] += [pin(failedPut/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordObjectPut01.lean','project/ShielddSecurity/TransferWordObjectPut01.lean','runs/01-TransferWordObjectPut01/stdout.txt','context/checked-pending-put-shape.json']]
pressurePut=DIAG/'transfer-word-object-put-20261011-02'
plan['pins'] += [pin(pressurePut/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordObjectPut01.lean','project/ShielddSecurity/TransferWordObjectPut01.lean','context/checked-pending-put-shape.json']]
plan['pins'].append(mapping['sct_pending_read_source_shape'])
pressureMembership=DIAG/'transfer-canonical-source-membership-20261011-01'
plan['pins'] += [pin(pressureMembership/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalSourceMembership01.lean','project/ShielddSecurity/TransferCanonicalSourceMembership01.lean','runs/01-TransferCanonicalSourceMembership01/stdout.txt']]
pressureStage=DIAG/'transfer-word-stage-order-20261011-01'
plan['pins'] += [pin(pressureStage/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageOrder01.lean','project/ShielddSecurity/TransferWordStageOrder01.lean','runs/01-TransferWordStageOrder01/stdout.txt']]
lintAdmission=DIAG/'transfer-word-stage-admission-20261011-01'
plan['pins'] += [pin(lintAdmission/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageAdmission01.lean','project/ShielddSecurity/TransferWordStageAdmission01.lean','runs/01-TransferWordStageAdmission01/stdout.txt']]
lintObject=lintAdmission/'project/ShielddSecurity/TransferWordStageAdmission01.olean'
assert lintObject.is_file()
plan['pins'].append(pin(lintObject))
pressureNumeric=DIAG/'transfer-word-stage-numeric-refinement-20261011-01'
assert not (pressureNumeric/'runs/01-TransferWordStageNumericRefinement01/stdout.txt').exists()
plan['pins'] += [pin(pressureNumeric/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageNumericRefinement01.lean','project/ShielddSecurity/TransferWordStageNumericRefinement01.lean']]
failedNumeric=DIAG/'transfer-word-stage-numeric-refinement-20261011-02'
plan['pins'] += [pin(failedNumeric/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageNumericRefinement01.lean','project/ShielddSecurity/TransferWordStageNumericRefinement01.lean','runs/01-TransferWordStageNumericRefinement01/stdout.txt']]
failedChecked=DIAG/'transfer-checked-word-stage-refinement-20261011-01'
plan['pins'] += [pin(failedChecked/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordStageRefinement01.lean','project/ShielddSecurity/TransferCheckedWordStageRefinement01.lean','runs/01-TransferCheckedWordStageRefinement01/stdout.txt']]
unrunChecked=DIAG/'transfer-checked-word-stage-refinement-20261011-03'
assert not (unrunChecked/'plan.json').exists() and not (unrunChecked/'events.jsonl').exists()
plan['pins'] += [pin(unrunChecked/n) for n in ['prepare_recipe.py','prepare.py']]
failedCheckedSecond=DIAG/'transfer-checked-word-stage-refinement-20261011-02'
plan['pins'] += [pin(failedCheckedSecond/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordStageRefinement01.lean','project/ShielddSecurity/TransferCheckedWordStageRefinement01.lean','runs/01-TransferCheckedWordStageRefinement01/stdout.txt']]
failedCache=DIAG/'transfer-word-stage-cache-publication-20261011-01'
plan['pins'] += [pin(failedCache/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageCachePublication01.lean','project/ShielddSecurity/TransferWordStageCachePublication01.lean','runs/01-TransferWordStageCachePublication01/stdout.txt']]
pressureCache=DIAG/'transfer-word-stage-cache-publication-20261011-02'
plan['pins'] += [pin(pressureCache/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageCachePublication01.lean','project/ShielddSecurity/TransferWordStageCachePublication01.lean','runs/01-TransferWordStageCachePublication01/stdout.txt']]
plan['pins'].append(mapping['checked_word_seal_source_shape'])
lintSeal=DIAG/'transfer-checked-word-seal-20261011-01'
plan['pins'] += [pin(lintSeal/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/checked-word-seal-shape.json','handwritten/TransferCheckedWordSeal01.lean','project/ShielddSecurity/TransferCheckedWordSeal01.lean','runs/01-TransferCheckedWordSeal01/stdout.txt','project/ShielddSecurity/TransferCheckedWordSeal01.olean']]
plan['pins'].append(pin(DIAG/'transfer-checked-word-seal-20261011-03/rejected-object-identity.json'))
pressureSeal=DIAG/'transfer-checked-word-seal-20261011-02'
plan['pins'] += [pin(pressureSeal/n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'context/checked-word-seal-shape.json', 'handwritten/TransferCheckedWordSeal01.lean', 'project/ShielddSecurity/TransferCheckedWordSeal01.lean', 'rejected-object-identity.json', 'runs/01-TransferCheckedWordSeal01/stdout.txt']]
pressureSealPublication=DIAG/'transfer-checked-word-seal-publication-20261011-01'
plan['pins'] += [pin(pressureSealPublication/n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferCheckedWordSealPublication01.lean', 'project/ShielddSecurity/TransferCheckedWordSealPublication01.lean']]
failedCheckedBlock=DIAG/'transfer-checked-word-block-driver-20261011-01'
plan['pins'] += [pin(failedCheckedBlock/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordBlockDriver01.lean','project/ShielddSecurity/TransferCheckedWordBlockDriver01.lean','runs/01-TransferCheckedWordBlockDriver01/stdout.txt']]
failedCheckedBlockSecond=DIAG/'transfer-checked-word-block-driver-20261011-02'
plan['pins'] += [pin(failedCheckedBlockSecond/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordBlockDriver01.lean','project/ShielddSecurity/TransferCheckedWordBlockDriver01.lean','runs/01-TransferCheckedWordBlockDriver01/stdout.txt']]
plan['pins'].append(mapping['fresh_snapshot_source_shape'])
plan['pins'].append(mapping['checked_word_accepted_source_shape'])
plan['pins'].append(mapping['scalar_canonical_add_source_shape'])
plan['pins'].append(mapping['scalar_canonical_sub_source_shape'])
plan['pins'].append(mapping['scalar_canonical_neg_source_shape'])
plan['pins'].append(mapping['scalar_program_family_source_shape'])
plan['pins'].append(mapping['scalar_wide_constructor_source_shape'])
plan['pins'].append(mapping['scalar_wide_byte_input_source_shape'])
plan['pins'].append(mapping['scalar_input_family_source_shape'])
plan['pins'].append(mapping['scalar_square_cross_source_shape'])
plan['pins'].append(mapping['scalar_square_shift_source_shape'])
plan['pins'].append(mapping['scalar_square_diagonal_source_shape'])
plan['pins'].append(mapping['scalar_square_product_source_shape'])
plan['pins'].append(mapping['scalar_pow_invariant_source_shape'])
plan['pins'].append(mapping['scalar_invert_machine_source_shape'])
plan['pins'].append(mapping['scalar_invert_chain_source_shape'])
plan['pins'].append(mapping['scalar_public_constants_source_shape'])
plan['pins'].append(mapping['scalar_extended_family_source_shape'])
plan['pins'].append(mapping['scalar_field_values_source_shape'])
plan['pins'].append(mapping['scalar_invert_field_source_shape'])
plan['pins'].append(mapping['scalar_pow_bit_integer_source_shape'])
plan['pins'].append(mapping['scalar_pow_field_source_shape'])
plan['pins'].append(pin(DIAG/'transfer-scalar-invert-chain-20261011-05/generate_source.py'))
failedAccepted=DIAG/'transfer-checked-word-accepted-input-20261011-01'
plan['pins'] += [pin(failedAccepted/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/checked-word-accepted-source-shape.json','handwritten/TransferCheckedWordAcceptedInput01.lean','project/ShielddSecurity/TransferCheckedWordAcceptedInput01.lean','runs/01-TransferCheckedWordAcceptedInput01/stdout.txt']]
failedAdd=DIAG/'transfer-scalar-canonical-add-20261011-01'
plan['pins'] += [pin(failedAdd/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-canonical-add-shape.json','handwritten/TransferScalarCanonicalAdd01.lean','project/ShielddSecurity/TransferScalarCanonicalAdd01.lean','runs/01-TransferScalarCanonicalAdd01/stdout.txt']]
failedSub=DIAG/'transfer-scalar-canonical-sub-20261011-01'
plan['pins'] += [pin(failedSub/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-canonical-sub-shape.json','handwritten/TransferScalarCanonicalSub01.lean','project/ShielddSecurity/TransferScalarCanonicalSub01.lean','runs/01-TransferScalarCanonicalSub01/stdout.txt']]
failedNeg=DIAG/'transfer-scalar-canonical-neg-20261011-01'
plan['pins'] += [pin(failedNeg/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-canonical-neg-shape.json','handwritten/TransferScalarCanonicalNeg01.lean','project/ShielddSecurity/TransferScalarCanonicalNeg01.lean','runs/01-TransferScalarCanonicalNeg01/stdout.txt']]
pressureNeg=DIAG/'transfer-scalar-canonical-neg-20261011-02'
plan['pins'] += [pin(pressureNeg/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-canonical-neg-shape.json','handwritten/TransferScalarCanonicalNeg01.lean','project/ShielddSecurity/TransferScalarCanonicalNeg01.lean']]
pressureWide=DIAG/'transfer-scalar-wide-constructor-20261011-01'
plan['pins'] += [pin(pressureWide/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-wide-constructor-shape.json','handwritten/TransferScalarWideConstructor01.lean','project/ShielddSecurity/TransferScalarWideConstructor01.lean']]
failedWide=DIAG/'transfer-scalar-wide-constructor-20261011-02'
plan['pins'] += [pin(failedWide/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-wide-constructor-shape.json','handwritten/TransferScalarWideConstructor01.lean','project/ShielddSecurity/TransferScalarWideConstructor01.lean','runs/01-TransferScalarWideConstructor01/stdout.txt']]
failedWideBytes=DIAG/'transfer-scalar-wide-byte-input-20261011-01'
plan['pins'] += [pin(failedWideBytes/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-wide-byte-input-shape.json','handwritten/TransferScalarWideByteInput01.lean','project/ShielddSecurity/TransferScalarWideByteInput01.lean','runs/01-TransferScalarWideByteInput01/stdout.txt']]
unrunInputFamily=DIAG/'transfer-scalar-input-family-20261011-01'
assert not (unrunInputFamily/'events.jsonl').exists()
plan['pins'] += [pin(unrunInputFamily/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-input-family-shape.json','handwritten/TransferScalarInputFamily01.lean','project/ShielddSecurity/TransferScalarInputFamily01.lean']]
pressureInputFamily=DIAG/'transfer-scalar-input-family-20261011-02'
plan['pins'] += [pin(pressureInputFamily/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-input-family-shape.json','handwritten/TransferScalarInputFamily01.lean','project/ShielddSecurity/TransferScalarInputFamily01.lean']]
failedInputFamily=DIAG/'transfer-scalar-input-family-20261011-03'
plan['pins'] += [pin(failedInputFamily/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-input-family-shape.json','handwritten/TransferScalarInputFamily01.lean','project/ShielddSecurity/TransferScalarInputFamily01.lean','runs/01-TransferScalarInputFamily01/stdout.txt']]
failedSquareCross=DIAG/'transfer-scalar-square-cross-20261011-01'
plan['pins'] += [pin(failedSquareCross/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-cross-shape.json','handwritten/TransferScalarSquareCross01.lean','project/ShielddSecurity/TransferScalarSquareCross01.lean','runs/01-TransferScalarSquareCross01/stdout.txt']]
unpreparedShift=DIAG/'transfer-scalar-square-shift-20261011-01'
assert not (unpreparedShift/'plan.json').exists()
plan['pins'] += [pin(unpreparedShift/n) for n in ['prepare_recipe.py','handwritten/TransferScalarSquareShift01.lean']]
failedShift=DIAG/'transfer-scalar-square-shift-20261011-02'
plan['pins'] += [pin(failedShift/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-shift-shape.json','handwritten/TransferScalarSquareShift01.lean','project/ShielddSecurity/TransferScalarSquareShift01.lean','runs/01-TransferScalarSquareShift01/stdout.txt']]
unpreparedShiftRename=DIAG/'transfer-scalar-square-shift-20261011-03'
assert not (unpreparedShiftRename/'plan.json').exists()
plan['pins'].append(pin(unpreparedShiftRename/'prepare_recipe.py'))
pressureDiagonal=DIAG/'transfer-scalar-square-diagonal-20261011-01'
assert (pressureDiagonal/'runs/01-TransferScalarSquareDiagonal01/stdout.txt').stat().st_size == 0
plan['pins'] += [pin(pressureDiagonal/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-diagonal-shape.json','handwritten/TransferScalarSquareDiagonal01.lean','project/ShielddSecurity/TransferScalarSquareDiagonal01.lean']]
plan['pins'].append(pin(pressureDiagonal/'runs/01-TransferScalarSquareDiagonal01/stdout.txt'))
unpreparedDiagonal=DIAG/'transfer-scalar-square-diagonal-20261011-02'
assert not (unpreparedDiagonal/'plan.json').exists()
plan['pins'] += [pin(unpreparedDiagonal/n) for n in ['prepare_recipe.py','prepare.py','execute_bounded.py','source-mapping.json','context/scalar-square-diagonal-shape.json','handwritten/TransferScalarSquareDiagonal01.lean','project/ShielddSecurity/TransferScalarSquareDiagonal01.lean']]
failedDiagonal=DIAG/'transfer-scalar-square-diagonal-20261011-03'
plan['pins'] += [pin(failedDiagonal/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-diagonal-shape.json','handwritten/TransferScalarSquareDiagonal01.lean','project/ShielddSecurity/TransferScalarSquareDiagonal01.lean','runs/01-TransferScalarSquareDiagonal01/stdout.txt']]
pressureSquareProduct=DIAG/'transfer-scalar-square-product-20261011-01'
priorSquareNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-product-shape.json','handwritten/TransferScalarSquareProduct01.lean','project/ShielddSecurity/TransferScalarSquareProduct01.lean']
if (pressureSquareProduct/'runs/01-TransferScalarSquareProduct01/stdout.txt').exists():
    priorSquareNames.append('runs/01-TransferScalarSquareProduct01/stdout.txt')
plan['pins'] += [pin(pressureSquareProduct/n) for n in priorSquareNames]
pressureInvertChain=DIAG/'transfer-scalar-invert-chain-20261011-01'
priorChainNames=['generate_source.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-chain-shape.json','generated/TransferScalarInvertChain01.lean','project/ShielddSecurity/TransferScalarInvertChain01.lean']
if (pressureInvertChain/'runs/01-TransferScalarInvertChain01/stdout.txt').exists():
    priorChainNames.append('runs/01-TransferScalarInvertChain01/stdout.txt')
plan['pins'] += [pin(pressureInvertChain/n) for n in priorChainNames]
failedInvertChain=DIAG/'transfer-scalar-invert-chain-20261011-02'
plan['pins'] += [pin(failedInvertChain/n) for n in ['generate_source.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-chain-shape.json','generated/TransferScalarInvertChain01.lean','project/ShielddSecurity/TransferScalarInvertChain01.lean','runs/01-TransferScalarInvertChain01/stdout.txt']]
failedInvertChainThird=DIAG/'transfer-scalar-invert-chain-20261011-03'
plan['pins'] += [pin(failedInvertChainThird/n) for n in ['generate_source.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-chain-shape.json','generated/TransferScalarInvertChain01.lean','project/ShielddSecurity/TransferScalarInvertChain01.lean','runs/01-TransferScalarInvertChain01/stdout.txt']]
failedInvertChainFourth=DIAG/'transfer-scalar-invert-chain-20261011-04'
plan['pins'] += [pin(failedInvertChainFourth/n) for n in ['generate_source.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-chain-shape.json','generated/TransferScalarInvertChain01.lean','project/ShielddSecurity/TransferScalarInvertChain01.lean','runs/01-TransferScalarInvertChain01/stdout.txt']]
pressureConstants=DIAG/'transfer-scalar-public-constants-20261011-01'
priorConstantNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-public-constants-shape.json','handwritten/TransferScalarPublicConstants01.lean','project/ShielddSecurity/TransferScalarPublicConstants01.lean']
if (pressureConstants/'runs/01-TransferScalarPublicConstants01/stdout.txt').exists():
    priorConstantNames.append('runs/01-TransferScalarPublicConstants01/stdout.txt')
plan['pins'] += [pin(pressureConstants/n) for n in priorConstantNames]
pressureInvertField=DIAG/'transfer-scalar-invert-field-20261012-01'
priorInvertFieldNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-field-shape.json','handwritten/TransferScalarInvertField01.lean','project/ShielddSecurity/TransferScalarInvertField01.lean']
assert not (pressureInvertField/'runs/01-TransferScalarInvertField01/stdout.txt').exists()
plan['pins'] += [pin(pressureInvertField/n) for n in priorInvertFieldNames]
failedInvertField=DIAG/'transfer-scalar-invert-field-20261012-02'
priorFailedInvertFieldNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-field-shape.json','handwritten/TransferScalarInvertField01.lean','project/ShielddSecurity/TransferScalarInvertField01.lean','runs/01-TransferScalarInvertField01/stdout.txt']
assert (failedInvertField/'runs/01-TransferScalarInvertField01/stdout.txt').exists()
plan['pins'] += [pin(failedInvertField/n) for n in priorFailedInvertFieldNames]
if (failedInvertField/'project/ShielddSecurity/TransferScalarInvertField01.olean').exists():
    plan['pins'].append(pin(failedInvertField/'project/ShielddSecurity/TransferScalarInvertField01.olean'))
plan['pins'] += [pin(DIAG/'transfer-scalar-inverse-correctness-20261012-01/prepare_recipe.py'),pin(DIAG/'transfer-scalar-inverse-correctness-20261012-01/handwritten/TransferScalarInverseCorrectness01.lean'),pin(DIAG/'transfer-scalar-inverse-correctness-20261012-04/prepare_recipe_from01.py')]
unrunInverse=DIAG/'transfer-scalar-inverse-correctness-20261012-02'
assert not (unrunInverse/'events.jsonl').exists()
unrunInverseNames=['prepare_recipe.py','prepare_recipe_from01.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-inverse-correctness-shape.json','handwritten/TransferScalarInverseCorrectness01.lean','project/ShielddSecurity/TransferScalarInverseCorrectness01.lean']
plan['pins'] += [pin(unrunInverse/n) for n in unrunInverseNames]
failedInverse=DIAG/'transfer-scalar-inverse-correctness-20261012-03'
failedInverseNames=['prepare_recipe.py','prepare_recipe_from01.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-inverse-correctness-shape.json','handwritten/TransferScalarInverseCorrectness01.lean','project/ShielddSecurity/TransferScalarInverseCorrectness01.lean','events.jsonl','runs/01-TransferScalarInverseCorrectness01/stdout.txt']
assert (failedInverse/'runs/01-TransferScalarInverseCorrectness01/stdout.txt').exists()
plan['pins'] += [pin(failedInverse/n) for n in failedInverseNames]
if (failedInverse/'project/ShielddSecurity/TransferScalarInverseCorrectness01.olean').exists():
    plan['pins'].append(pin(failedInverse/'project/ShielddSecurity/TransferScalarInverseCorrectness01.olean'))
unrunPower=DIAG/'transfer-scalar-pow-field-20261012-01'
assert not (unrunPower/'events.jsonl').exists()
unrunPowerNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean']
plan['pins'] += [pin(unrunPower/n) for n in unrunPowerNames]
failedPower=DIAG/'transfer-scalar-pow-field-20261012-02'
failedPowerNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean','events.jsonl','runs/01-TransferScalarPowField01/stdout.txt']
plan['pins'] += [pin(failedPower/n) for n in failedPowerNames]
unrunNarrowPower=DIAG/'transfer-scalar-pow-field-20261012-03'
assert not (unrunNarrowPower/'events.jsonl').exists()
unrunNarrowPowerNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean']
plan['pins'] += [pin(unrunNarrowPower/n) for n in unrunNarrowPowerNames]
pressurePower=DIAG/'transfer-scalar-pow-field-20261012-04'
pressurePowerNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean','events.jsonl']
pressureStdout=pressurePower/'runs/01-TransferScalarPowField01/stdout.txt'
if pressureStdout.exists():pressurePowerNames.append('runs/01-TransferScalarPowField01/stdout.txt')
plan['pins'] += [pin(pressurePower/n) for n in pressurePowerNames]
unrunPowerFifth=DIAG/'transfer-scalar-pow-field-20261012-05'
assert not (unrunPowerFifth/'events.jsonl').exists()
unrunPowerFifthNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean']
plan['pins'] += [pin(unrunPowerFifth/n) for n in unrunPowerFifthNames]
unpreparedPowerSixth=DIAG/'transfer-scalar-pow-field-20261012-06'
assert not (unpreparedPowerSixth/'plan.json').exists() and not (unpreparedPowerSixth/'events.jsonl').exists()
unpreparedPowerSixthNames=['prepare_recipe.py','prepare.py','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean']
plan['pins'] += [pin(unpreparedPowerSixth/n) for n in unpreparedPowerSixthNames]
plan['pins'].append(pin(DIAG/'transfer-scalar-pow-field-owned-floor-20261012-06/composition-review.json'))
pressurePowerSeventh=DIAG/'transfer-scalar-pow-field-20261012-07'
pressurePowerSeventhNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean','events.jsonl']
assert not (pressurePowerSeventh/'runs/01-TransferScalarPowField01/stdout.txt').exists()
plan['pins'] += [pin(pressurePowerSeventh/n) for n in pressurePowerSeventhNames]
plan['artifact_policy'] = 'One source and bounded reports/object; complete163-module qualified word root and unchanged original qualified Core floor; inverse/prime packet preserved separately.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit guards unchanged.'
plan['invocation'] = 'Autonomous serial narrow source writer preparation proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'SCALAR_POW_FIELD_COMPLETE_WORD_BRANCH_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 6, 'inherited_audits': len(audits), 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
dump(ROOT / 'review.json', review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
