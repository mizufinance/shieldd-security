"""Prepare overlay-derived current volume refusal on the complete qualified closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
UPSTREAM = DIAG / 'transfer-authenticated-boundary-source-20261011-01'
POOL = DIAG / 'transfer-writer-recovery-join-owned-floor-20261011-01'
MODULE = 'TransferWriterRecoveryJoin01'

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
stdout = UPSTREAM / 'runs/01-TransferAuthenticatedBoundarySource01/stdout.txt'
current = m.audit(stdout.read_text(), target['audit_names'])
assert len(current) == 9 and current == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
assert set(audits).isdisjoint(current)
audits.update(current)
records.append(('TransferAuthenticatedBoundarySource01', target['source'], events[-1]['result']['objects'][0]))
inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferAuthenticatedBoundarySource01.lean', 'project/ShielddSecurity/TransferAuthenticatedBoundarySource01.lean']]
inputs.append(pin(stdout))
legacy = DIAG / 'transfer-readback-recovery-publication-20261010-02'
legacy_plan = json.loads((legacy / 'plan.json').read_bytes())
legacy_events = [json.loads(row) for row in (legacy / 'events.jsonl').read_text().splitlines()]
legacy_targets = {row['module']: row for row in legacy_plan['targets']}
legacy_results = {row['module']: row['result'] for row in legacy_events if row['event'] == 'attempt_finished'}
assert all(row['status'] == 'passed' for row in legacy_results.values())
shared = next(row for row in records if row[0] == 'TransferReadback')
assert shared[1] == legacy_targets['TransferReadback']['source'] and shared[2] == legacy_results['TransferReadback']['objects'][0]
assert {name: audits[name] for name in legacy_targets['TransferReadback']['audit_names']} == legacy_results['TransferReadback']['audits']
bank = legacy_targets['TransferBankRecovery']; bank_result = legacy_results['TransferBankRecovery']
bank_stdout = legacy / 'runs/02-TransferBankRecovery/stdout.txt'
bank_reports = m.audit(bank_stdout.read_text(), bank['audit_names'])
assert len(bank_reports) == 10 and bank_reports == bank_result['audits']
assert pin(bank_stdout) == bank_result['stdout'] and pin(bank['source']['path']) == bank['source']
assert bank['source']['sha256'] == '446f60161277bab78888eb47dc528a8bc0b9c05283ecf44a59424b0860faa294'
assert pin(bank_result['objects'][0]['path']) == bank_result['objects'][0]
assert bank_result['objects'][0]['sha256'] == '044a20e3830fbe861cfdfa7fd9fbf3df9cd0dc130105999d7f702882a180fd14'
assert bank_result['stdout']['sha256'] == '6f1e114a35da29dcc593cbeeffe4888e811f3493e4187c09472f470395bb4afc'
assert set(audits).isdisjoint(bank_reports) and not any(row[0] == 'TransferBankRecovery' for row in records)
audits.update(bank_reports)
records.append(('TransferBankRecovery', bank['source'], bank_result['objects'][0]))
inputs += [pin(legacy / name) for name in ['plan.json', 'execute_bounded.py', 'events.jsonl', 'source-mapping.json', 'prepare.py', 'review.json']]
inputs += [bank['source'], bank_result['objects'][0], pin(bank_stdout)]
assert len(records) == 57 and len(audits) == 570
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
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 57, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete fifty-seven-module first owned root; 570 inherited full reports; shared StateDelta/Readback included exactly once. Original BankRecovery10 selected once without replay; WriterPublication not selected. Exact qualified source/object closure and complete reports reused without replay. Exact copied objects add no new replay or Rust refinement.'}
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
for relative in ['crates/core/app/src/app/permanent_writer.rs', 'crates/core/component/sct/src/permanent_nullifiers/store.rs', 'crates/core/component/sct/src/permanent_nullifiers.rs']:
    row = pin(runtime / relative)
    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
    runtime_rows[row['path']] = row
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),
    'interfaces': prior_mapping['interfaces'] + ['Original BankRecovery10 is an independently qualified model of recovery controls/observed roots/history/health; exact legacy source/object/reports reused, no imported replay and no duplicate Readback reports. Adapter only maps modeled returned recovery error to source writer completion callback success. Supplied store denotes recovery invocation observation, not defined to equal desired participant state; native state threading/same lock/partition poison snapshots/rollback-other-partition frames and durable I/O remain separate obligations. Recovery clean establishes ready/roots/boundary/history while partition health stays independently observed healthyAfter. Post-completion capacity error preserves source owner Ready and modeled observed recovery without rollback inference.'],
    'scope': 'Model composition of actual-source PermanentWriter participant/commit/capacity order with independently qualified original BankRecovery10, reused once with original source/object/full type/axiom reports and shared Readback17 unchanged. Recovery environment denotes independently observed store at completion invocation. Completion callback reports recovery returned error status; completed source participants derive clean recovery, ready/current roots/exact frozen boundary/16 roots/retained-history validity and independently observed partition health. Whole returned source commit derives same Ready owner/returned boundary and observed recovered store boundary/roots. Capacity error preserves Ready/new boundary and completed recovery; failed recovery prevents participant completion and blocks owner API status. Six fresh reports (two program definitions, four proofs), 570 original inherited reports/57 owned modules, strict finite/physical guards unchanged. Native prior participant-to-recovery state threading, current poison snapshots/intermediate readers, source complete/recovery/rollback/partition frames, locks/owner/Clone/typed values/physical I/O/durability remain explicit correspondence obligations; original recovery model is not relabeled native proof. No native/control/full Transfer certification or inferred healthy partitions/error rollback.'}
mapping_file = ROOT / 'source-mapping.json'
dump(mapping_file, mapping)
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': MODULE, 'source': pin(target_source), 'predecessor_source': pin(handwritten),
    'imports': ['ShielddSecurity.TransferAuthenticatedBoundarySource01', 'ShielddSecurity.TransferBankRecovery'],
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
plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'SOURCE_WRITER_COMPLETION_ORIGINAL_RECOVERY_MODEL_JOIN'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh source-writer/qualified-recovery model composition; original BankRecovery10 object/reports selected once with exact shared Readback identity and no replay. Native state threading/health/ownership/refinement remain explicit. Guards unchanged.'
plan['artifact_policy'] = 'One source and bounded reports/object; complete fifty-seven-module owned root and reachable core floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit guards unchanged.'
plan['invocation'] = 'Autonomous serial narrow source writer preparation proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'WRITER_RECOVERY_JOIN_COMPLETE_FIFTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 6, 'inherited_audits': 570, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
dump(ROOT / 'review.json', review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
