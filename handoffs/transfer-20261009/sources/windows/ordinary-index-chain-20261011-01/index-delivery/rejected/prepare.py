"""Prepare overlay-derived current volume refusal on the complete qualified closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
UPSTREAM = DIAG / 'transfer-bound-ordinary-source-20261011-02'
POOL = DIAG / 'transfer-ordinary-index-delivery-owned-floor-20261011-01'
MODULE = 'TransferOrdinaryIndexDelivery01'

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
stdout = UPSTREAM / 'runs/01-TransferBoundOrdinarySource01/stdout.txt'
current = m.audit(stdout.read_text(), target['audit_names'])
assert len(current) == 12 and current == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
assert set(audits).isdisjoint(current)
audits.update(current)
records.append(('TransferBoundOrdinarySource01', target['source'], events[-1]['result']['objects'][0]))
inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferBoundOrdinarySource01.lean', 'project/ShielddSecurity/TransferBoundOrdinarySource01.lean']]
inputs.append(pin(stdout))
assert len(records) == 13 and len(audits) == 174
inspection = DIAG / 'transfer-index-inspection-20261011-02'
inspection_plan = json.loads((inspection / 'plan.json').read_bytes())
inspection_pool = json.loads(Path(inspection_plan['owned_import_pool']['path']).read_bytes())
inspection_events = [json.loads(s) for s in (inspection / 'events.jsonl').read_text().splitlines()]
assert len(inspection_events) == 2 and inspection_events[-1]['result']['status'] == 'passed'
inspection_target = inspection_plan['targets'][0]
inspection_stdout = inspection / 'runs/01-TransferIndexInspectionFacts01/stdout.txt'
inspection_reports = m.audit(inspection_stdout.read_text(), inspection_target['audit_names'])
assert len(inspection_reports) == 16 and inspection_reports == inspection_events[-1]['result']['audits']
assert pin(inspection_stdout) == inspection_events[-1]['result']['stdout']
for row in inspection_pool['selected'] + [{'module': 'TransferIndexInspectionFacts01', 'source': inspection_target['source'], 'object': inspection_events[-1]['result']['objects'][0]}]:
    old = next((r for r in records if r[0] == row['module']), None)
    if old:
        assert old == (row['module'], row['source'], row['object'])
    else:
        records.append((row['module'], row['source'], row['object']))
for name, report in {**inspection_pool['inherited_public_reports'], **inspection_reports}.items():
    assert name not in audits or audits[name] == report
    audits[name] = report
inputs += inspection_pool['input_records']
inputs += [pin(inspection / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferIndexInspectionFacts01.lean', 'project/ShielddSecurity/TransferIndexInspectionFacts01.lean']]
inputs.append(pin(inspection_stdout))
assert len(records) == 16 and len(audits) == 221
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
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 16, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete sixteen-module first owned root; 221 inherited full reports; shared cache/raw source objects and 28 full reports counted once. Exact copied objects add no new replay or Rust refinement.'}
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
runtime_rows = json.loads((UPSTREAM / 'source-mapping.json').read_bytes())['runtime_sources'] + json.loads((inspection / 'source-mapping.json').read_bytes())['runtime_sources']
runtime_union = {}
for row in runtime_rows:
    assert pin(row['path']) == row
    assert row['path'] not in runtime_union or runtime_union[row['path']] == row
    runtime_union[row['path']] = row
mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': list(runtime_union.values()),
    'interfaces': ['Generic body adapter is instantiated with the qualified exact-Item Ordinary source program; extractor/token/proof provenance remains upstream',
        'Loaded immutable SCT, Rust CloneCOW/panic/tree/key/value/source/event codecs and store authentication remain inherited interfaces',
        'Transaction conversion, byte-key projection, big-endian count codec and actual index storage reads require source correspondence',
        'Run commit denotes applying child cache to original parent; it does not imply block seal or durable multi-store publication',
        'Returned error discard remains scoped; native Host panic/queue retry and all native controls remain separate',
        'No semantic negative-control, native or full Transfer certification credit'],
    'scope': 'Concrete per-transaction index program follows the actual body and height read. Whole enclosing success derives actual body success/cache, current height, index inspection witness and exact three NV writes applied to original parent; conversion, absent identifier, count read/decode and checked ordinal are recovered. Index preserves body V/object/event effects and queue exactly. Instantiating the qualified bound Ordinary body derives exact Item re-extraction, initially absent parent volume entry and both visible markers from the whole delivery success under explicit volume key separation. No desired successful body, index witness or target cache is a premise. Rust/proof/representation/store/native/block/durability and full Transfer remain open.'}
mapping_file = ROOT / 'source-mapping.json'
dump(mapping_file, mapping)
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': MODULE, 'source': pin(target_source), 'predecessor_source': pin(handwritten),
    'imports': ['ShielddSecurity.TransferBoundOrdinarySource01', 'ShielddSecurity.TransferIndexInspectionFacts01'],
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
plan['kind'] = 'ORDINARY_BODY_AND_CONCRETE_TRANSACTION_INDEX_WHOLE_DELIVERY_SUCCESS'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh finite source over exact bound-body and index-inspection union; shared cache/raw sources, objects and reports agree. No ancestors replayed, desired result premise or guard/audit relaxation.'
plan['artifact_policy'] = 'One source and bounded reports/object; complete sixteen-module owned root and reachable core floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit guards unchanged.'
plan['invocation'] = 'Autonomous serial narrow current-volume overlay source proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'ORDINARY_INDEX_DELIVERY_COMPLETE_SIXTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 6, 'inherited_audits': 221, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
dump(ROOT / 'review.json', review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
