"""Prepare overlay-derived current volume refusal on the complete qualified closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
UPSTREAM = DIAG / 'transfer-ordinary-decodable-index-20261011-01'
POOL = DIAG / 'transfer-deferred-count-walk-owned-floor-20261011-01'
MODULE = 'TransferDeferredCountWalk01'

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
stdout = UPSTREAM / 'runs/01-TransferOrdinaryDecodableIndex01/stdout.txt'
current = m.audit(stdout.read_text(), target['audit_names'])
assert len(current) == 1 and current == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
assert set(audits).isdisjoint(current)
audits.update(current)
records.append(('TransferOrdinaryDecodableIndex01', target['source'], events[-1]['result']['objects'][0]))
inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferOrdinaryDecodableIndex01.lean', 'project/ShielddSecurity/TransferOrdinaryDecodableIndex01.lean']]
inputs.append(pin(stdout))
DEFERRED = DIAG / 'transfer-deferred-queue-model-20261010-03'
dp = json.loads((DEFERRED / 'plan.json').read_bytes())
de = [json.loads(x) for x in (DEFERRED / 'events.jsonl').read_text().splitlines()]
assert len(de) == 2 and de[-1]['result']['status'] == 'passed'
dt = dp['targets'][0]
ds = DEFERRED / 'runs/01-TransferDeferredQueueSourceModel01/stdout.txt'
da = m.audit(ds.read_text(), dt['audit_names'])
assert len(da) == 17 and da == de[-1]['result']['audits'] and set(da).isdisjoint(audits)
assert pin(ds) == de[-1]['result']['stdout']
assert dp['external_floor'] == plan['external_floor']
for shared in dp['owned_imports']:
    assert any(shared['sha256'] == obj['sha256'] and shared['bytes'] == obj['bytes'] for _, _, obj in records)
records.append(('TransferDeferredQueueSourceModel01',dt['source'],de[-1]['result']['objects'][0]))
audits.update(da)
inputs += [pin(DEFERRED / n) for n in ['plan.json','events.jsonl','execute_bounded.py','source-mapping.json','project/ShielddSecurity/TransferDeferredQueueSourceModel01.lean']]
inputs.append(pin(ds))

assert len(records) == 26 and len(audits) == 301
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
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 26, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete twenty-six-module first owned root; 301 inherited full reports. Exact qualified source/object closure and complete reports reused without replay. Exact copied objects add no new replay or Rust refinement.'}
composition_file = POOL / 'composition-review.json'
dump(composition_file, composition)
handwritten = ROOT / 'handwritten' / (MODULE + '.lean')
source = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 4 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', source, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(source))
target_source = ROOT / 'project/ShielddSecurity' / handwritten.name
target_source.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target_source)
runtime = Path('C:/src/shieldd-pr160-844389ee')
prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Arbitrary-list deferred count recurrence with actual modeled current NV reads and concrete u64 codec: a successful index step derives the decoded next ordinal and increment; successful complete walk derives initial count plus queue length and excludes u64 wrap. Caller supplies only original input-state count observation and whole walk success, not per-step success/increment/desired cache or final counter. Reads remain availability-sensitive; genuine Rust/ownership/key/crypto/native/Host/durability and full Transfer correspondence remain open. No native or semantic negative-control credit.'}
mapping_file = ROOT / 'source-mapping.json'
dump(mapping_file, mapping)
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': MODULE, 'source': pin(target_source), 'predecessor_source': pin(handwritten),
    'imports': ['ShielddSecurity.TransferOrdinaryDecodableIndex01','ShielddSecurity.TransferDeferredQueueSourceModel01'],
    'audit_names': ['ShielddSecurity.' + MODULE + '.' + n for n in names]}]
baseline = json.loads(Path(plan['preservation']['path']).read_bytes())
plan['pins'] = baseline['protected'] + baseline['foreign'] + inputs + plan['owned_imports']
plan['pins'] += [pin(p) for p in [Path(__file__), ROOT / 'prepare_recipe.py', runner, handwritten, target_source, composition_file, mapping_file]]
plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'ARBITRARY_DEFERRED_WALK_DERIVES_COUNT_INCREASE_WITHOUT_U64_WRAP'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh symbolic arbitrary-list deferred count recurrence on exact merged qualified closures; all inherited proofs and guards unchanged.'
plan['artifact_policy'] = 'One source and bounded reports/object; complete twenty-six-module owned root and reachable core floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit guards unchanged.'
plan['invocation'] = 'Autonomous serial narrow current-volume overlay source proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'DEFERRED_COUNT_WALK_COMPLETE_TWENTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 4, 'inherited_audits': 301, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
dump(ROOT / 'review.json', review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
