"""Prepare overlay-derived current volume refusal on the complete qualified closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
UPSTREAM = DIAG / 'transfer-durable-write-source-20261011-01'
POOL = DIAG / 'transfer-record-read-bound-owned-floor-20261011-01'
MODULE = 'TransferRecordReadBound01'

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
stdout = UPSTREAM / 'runs/01-TransferDurableWriteSource01/stdout.txt'
current = m.audit(stdout.read_text(), target['audit_names'])
assert len(current) == 8 and current == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
assert set(audits).isdisjoint(current)
audits.update(current)
records.append(('TransferDurableWriteSource01', target['source'], events[-1]['result']['objects'][0]))
inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferDurableWriteSource01.lean', 'project/ShielddSecurity/TransferDurableWriteSource01.lean']]
inputs.append(pin(stdout))
assert len(records) == 59 and len(audits) == 584
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
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 59, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete fifty-nine-module first owned root; 584 inherited full reports; shared StateDelta/Readback and original BankRecovery10 included exactly once. Exact qualified source/object closure and complete reports reused without replay. Exact copied objects add no new replay or Rust refinement.'}
composition_file = POOL / 'composition-review.json'
dump(composition_file, composition)
handwritten = ROOT / 'generated' / (MODULE + '.lean')
source = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 8 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
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
    'interfaces': prior_mapping['interfaces'] + ['Generated constant uses restricted arithmetic parsing of exact pinned Rust MAX_RECORD_BYTES expression and asserts source take/read_to_end/size-check return structure. Primitive readToEnd callback carries actual returned bytes or error; take limit passed explicitly. Native file/read/Take consumption or actual returned byte allocation bounds are not assumed from source identity; read errors may have consumed partial data and no physical rollback inferred. Model Nat length check corresponds to native usize as u64 on supported typed 32/64-bit domain; u8 data validity, serde/owner/OS/async correspondence remains explicit. Formal oversized/refusal proof is not an executed negative control.'],
    'scope': 'Generated exact source MAX_RECORD_BYTES expression 4*1024*1024 and checked source read_record take(MAX_RECORD_BYTES+1)/read_to_end/returned byte length check. Source take limit is one beyond record cap and proved below 32/64-bit word ranges. Whole returned record derives exact observed read_to_end bytes at source take limit and length at most 4194304; oversized returned bytes and read errors refuse without default records. Eight reports (four data/program definitions, four proofs), maintained generator plus byte-identical independent regeneration; finite/physical/strict audit guards unchanged. Native File/Take/Read partial read semantics, allocation/typed u8/usize-to-u64 supported word embedding/ownership/serde/OS state and whole input consumption remain interfaces. Model Nat length reflects native cast only on supported typed 32/64-bit domain. No native/control/full Transfer certification and no semantic-negative-control credit from formal refusal proofs.'}
mapping_file = ROOT / 'source-mapping.json'
dump(mapping_file, mapping)
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': MODULE, 'source': pin(target_source), 'predecessor_source': pin(handwritten),
    'imports': ['ShielddSecurity.TransferDurableWriteSource01'],
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
regenerated = DIAG / 'transfer-record-read-regeneration-20261011-01'
assert (regenerated / 'generated' / (MODULE + '.lean')).read_bytes() == handwritten.read_bytes()
plan['pins'] += [pin(ROOT / 'generate.py'), pin(ROOT / 'generation.json'), pin(regenerated / 'generation.json'), pin(regenerated / 'generated' / (MODULE + '.lean'))]
plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'SOURCE_RECORD_READ_TAKE_LIMIT_RETURNED_BYTE_BOUND_AND_REFUSALS'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh maintained source byte cap/take/read check model and independent exact regeneration; no generated hand edits, ancestor replay or native control credit. Guards unchanged.'
plan['artifact_policy'] = 'One source and bounded reports/object; complete fifty-nine-module owned root and reachable core floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit guards unchanged.'
plan['invocation'] = 'Autonomous serial narrow source writer preparation proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'RECORD_READ_BOUND_COMPLETE_FIFTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 8, 'inherited_audits': 584, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
dump(ROOT / 'review.json', review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
