"""Compose raw program success with delivery over a complete two-module owned root."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
RAW = DIAG / 'transfer-raw-state-program-20261011-02'
POOL = DIAG / 'transfer-raw-delivery-owned-floor-20261011-02'
def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
assert not (ROOT / 'plan.json').exists() and not POOL.exists()
runner = ROOT / 'execute_bounded.py'
assert pin(RAW / runner.name)['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(RAW / runner.name, runner)
spec = importlib.util.spec_from_file_location('raw_delivery_exact_auditor', runner)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((RAW / 'plan.json').read_bytes())
existing = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
events = [json.loads(s) for s in (RAW / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
audits = m.audit((RAW / 'runs/01-TransferRawStateProgram01/stdout.txt').read_text(), plan['targets'][0]['audit_names'])
assert len(audits) == 16 and audits == events[-1]['result']['audits']
selected = []
POOL.mkdir()
inputs = existing['input_records'] + [pin(RAW / name) for name in [
    'plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferRawStateProgram01.lean', 'project/ShielddSecurity/TransferRawStateProgram01.lean',
    'runs/01-TransferRawStateProgram01/stdout.txt']]
records = [(r['module'], r['source'], r['object']) for r in existing['selected']]
records += [('TransferRawStateProgram01', plan['targets'][0]['source'], events[-1]['result']['objects'][0])]
for module, source, obj in records:
    assert pin(source['path']) == source and pin(obj['path']) == obj
    copy = POOL / 'modules/ShielddSecurity' / (module + '.olean')
    copy.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(obj['path'], copy)
    assert pin(copy)['sha256'] == obj['sha256']
    selected.append({'module': module, 'source': source, 'object': obj, 'copy': pin(copy)})
    inputs += [source, obj]
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 2, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': {**existing['inherited_public_reports'], **audits},
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete exact first owned package for the actual two-module closure: accepted cache/delivery model plus freshly qualified failure-aware raw program. Twenty-eight full inherited public type/standard-axiom reports checked. Copies establish identity and import completeness, not new replay or Rust refinement.'}
composition_file = POOL / 'composition-review.json'
composition_file.write_bytes((json.dumps(composition, indent=2, sort_keys=True) + '\n').encode())
handwritten = ROOT / 'handwritten/TransferRawDeliveryComposition01.lean'
text = handwritten.read_text()
names = re.findall(r'^theorem ([A-Za-z0-9_]+)', m.code_only(text), re.M)
assert len(names) == 5 and re.findall(r'^#check @([^\n]+)', text, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', text, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(text))
target = ROOT / 'project/ShielddSecurity' / handwritten.name
target.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target)
mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': json.loads((RAW / 'source-mapping.json').read_bytes())['runtime_sources'],
    'success': 'Recover the successful raw outcome from the adapter by an iff, then use the unchanged delivery run to derive actual child cache, index preparation, parent apply, events and deferred append. The replacement execute field leaves the original height/index callbacks unchanged.',
    'modes': 'Deferred success derives a successful height observation, applies the raw program cache and appends the exact supplied transaction. PerTx success derives successful height and index observations, applies the resulting index cache and leaves the earlier deferred queue unchanged.',
    'scope': 'Functional source-order composition only. Raw callback/primitive effects, transaction codec/projection, Rust aliases/Clone/COW and complete state/durability correspondence remain explicit interfaces. Source identity does not establish semantic refinement. Accepted finite runtime controls remain separate evidence; no new native control or full Transfer certificate is claimed.'}
mapping_file = ROOT / 'source-mapping.json'
mapping_file.write_bytes((json.dumps(mapping, indent=2, sort_keys=True) + '\n').encode())
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': 'TransferRawDeliveryComposition01', 'source': pin(target),
    'predecessor_source': pin(handwritten), 'imports': ['ShielddSecurity.TransferRawStateProgram01'],
    'audit_names': ['ShielddSecurity.TransferRawDeliveryComposition01.' + name for name in names]}]
baseline = json.loads(Path(plan['preservation']['path']).read_bytes())
plan['pins'] = baseline['protected'] + baseline['foreign'] + inputs + plan['owned_imports']
plan['pins'] += [pin(p) for p in [Path(__file__), runner, handwritten, target, composition_file, mapping_file]]
plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'NARROW_ACTUAL_RAW_SUCCESS_CACHE_AND_DELIVERY_INDEX_MODE_COMPOSITION'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'None; first source attempt. Existing inherited sources unchanged; five new reusable symbolic success/index-mode composition lemmas.'
plan['artifact_policy'] = 'One new source and bounded receipts/object; exact two-module complete first owned root, complete reachable core external floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit protections unchanged.'
plan['invocation'] = 'Autonomous serial narrow composition proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'SOURCE_AND_COMPLETE_TWO_MODULE_OWNED_IMPORTS_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 5, 'inherited_audits': 28, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
