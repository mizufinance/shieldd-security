"""Prepare overlay-derived current volume refusal on the complete qualified closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
UPSTREAM = DIAG / 'transfer-ordinary-max-count-20261011-02'
POOL = DIAG / 'transfer-ordinary-decodable-index-owned-floor-20261011-01'
MODULE = 'TransferOrdinaryDecodableIndex01'

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
stdout = UPSTREAM / 'runs/01-TransferOrdinaryMaxCount01/stdout.txt'
current = m.audit(stdout.read_text(), target['audit_names'])
assert len(current) == 6 and current == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
assert set(audits).isdisjoint(current)
audits.update(current)
records.append(('TransferOrdinaryMaxCount01', target['source'], events[-1]['result']['objects'][0]))
inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'generated/TransferOrdinaryMaxCount01.lean', 'project/ShielddSecurity/TransferOrdinaryMaxCount01.lean']]
inputs.append(pin(stdout))
assert len(records) == 25 and len(audits) == 283
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
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 25, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete twenty-five-module first owned root; 283 inherited full reports. Exact qualified source/object closure and complete reports reused without replay. Exact copied objects add no new replay or Rust refinement.'}
composition_file = POOL / 'composition-review.json'
dump(composition_file, composition)
handwritten = ROOT / 'handwritten' / (MODULE + '.lean')
source = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 1 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', source, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(source))
target_source = ROOT / 'project/ShielddSecurity' / handwritten.name
target_source.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target_source)
runtime = Path('C:/src/shieldd-pr160-844389ee')
prior_mapping = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Whole same-action Ordinary per-transaction success with actual modeled current NV reads, concrete eight-byte ordinal key encoding and concrete u64 value codec derives exact compared extraction/conversion, checked next ordinal, original volume absence and both marker values, payload/identifier/count writes, eight-byte lengths, valid byte ranges and decoder roundtrips for both stored ordinal values. The same projected source namespaces derive volume key separation. Desired codec, stored-value or successful raw-body postconditions are never caller premises. Rust key prefix/byte projection/ownership/proof/token/crypto/tree/native/block/durability correspondence remains explicit. No new native or semantic control credit; full Transfer remains open.'}
mapping_file = ROOT / 'source-mapping.json'
dump(mapping_file, mapping)
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': MODULE, 'source': pin(target_source), 'predecessor_source': pin(handwritten),
    'imports': ['ShielddSecurity.TransferOrdinaryMaxCount01'],
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
plan['kind'] = 'WHOLE_ORDINARY_SUCCESS_DERIVES_DECODABLE_CONCRETE_U64_INDEX_VALUES'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh handwritten whole-call concrete ordinal key/value codec success composition; all inherited proofs and guards unchanged.'
plan['artifact_policy'] = 'One source and bounded reports/object; complete twenty-five-module owned root and reachable core floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit guards unchanged.'
plan['invocation'] = 'Autonomous serial narrow current-volume overlay source proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'ORDINARY_DECODABLE_INDEX_COMPLETE_TWENTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 1, 'inherited_audits': 283, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
dump(ROOT / 'review.json', review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
