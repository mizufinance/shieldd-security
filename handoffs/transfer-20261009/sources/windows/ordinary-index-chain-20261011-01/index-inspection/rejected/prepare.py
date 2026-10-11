"""Prepare inspection/key/entry facts over the complete four-module qualified closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PREVIOUS = DIAG / 'transfer-index-writer-model-20261011-02'
POOL = DIAG / 'transfer-index-inspection-owned-floor-20261011-01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

assert not (ROOT / 'plan.json').exists() and not POOL.exists()
runner = ROOT / 'execute_bounded.py'
assert pin(PREVIOUS / runner.name)['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(PREVIOUS / runner.name, runner)
spec = importlib.util.spec_from_file_location('inspection_exact_auditor', runner)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((PREVIOUS / 'plan.json').read_bytes())
existing = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
events = [json.loads(s) for s in (PREVIOUS / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
audits = m.audit((PREVIOUS / 'runs/01-TransferIndexWriterModel01/stdout.txt').read_text(), plan['targets'][0]['audit_names'])
assert len(audits) == 26 and audits == events[-1]['result']['audits']
selected = []
POOL.mkdir()
inputs = existing['input_records'] + [pin(PREVIOUS / name) for name in [
    'plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferIndexWriterModel01.lean', 'project/ShielddSecurity/TransferIndexWriterModel01.lean',
    'runs/01-TransferIndexWriterModel01/stdout.txt']]
records = [(r['module'], r['source'], r['object']) for r in existing['selected']]
records += [('TransferIndexWriterModel01', plan['targets'][0]['source'], events[-1]['result']['objects'][0])]
for module, source, obj in records:
    assert pin(source['path']) == source and pin(obj['path']) == obj
    copy = POOL / 'modules/ShielddSecurity' / (module + '.olean')
    copy.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(obj['path'], copy)
    assert pin(copy)['sha256'] == obj['sha256']
    selected.append({'module': module, 'source': source, 'object': obj, 'copy': pin(copy)})
    inputs += [source, obj]
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 4, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': {**existing['inherited_public_reports'], **audits},
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete exact first owned package for the four-module transitive closure. Fifty-nine full inherited declaration types/standard axioms checked. Qualified object copies add no new replay or Rust refinement.'}
composition_file = POOL / 'composition-review.json'
composition_file.write_bytes((json.dumps(composition, indent=2, sort_keys=True) + '\n').encode())
handwritten = ROOT / 'handwritten/TransferIndexInspectionFacts01.lean'
source = handwritten.read_text()
names = re.findall(r'^(?:abbrev|inductive|structure|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 16 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', source, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(source))
target = ROOT / 'project/ShielddSecurity' / handwritten.name
target.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target)
prior_mapping = json.loads((PREVIOUS / 'source-mapping.json').read_bytes())
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'inspection': 'Success inversion recovers conversion, absent duplicate-ID observation, count read/decode and checked next ordinal. The checked increment proves next=current+1 strictly below 2^64. Conversion/duplicate/overflow refusals derive the exact intended semantic error in the modeled program.',
    'byte_keys': 'ASCII byte suffixes /count, /entry/ and /id/ are unequal for any shared height prefix and any appended ordinal/ID bytes. Equality-preserving projection into Nat keys is an explicit representation premise, with projected key separation derived from byte facts rather than assumed.',
    'values': 'Successful inspection and the explicit three-write program derive exact entry payload, identifier ordinal, and next count values. No desired output cache or arbitrary poststate premise.',
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Functional inspection, actual byte-tag separation and exact three-write values only. Transaction/codec/storage/Rust-cache correspondence, projection representation, native controls and full Transfer remain explicit open obligations. Source hashes establish identity; no new native/negative-control/full certification credit.'}
mapping_file = ROOT / 'source-mapping.json'
mapping_file.write_bytes((json.dumps(mapping, indent=2, sort_keys=True) + '\n').encode())
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': 'TransferIndexInspectionFacts01', 'source': pin(target),
    'predecessor_source': pin(handwritten), 'imports': ['ShielddSecurity.TransferIndexWriterModel01'],
    'audit_names': ['ShielddSecurity.TransferIndexInspectionFacts01.' + name for name in names]}]
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
plan['kind'] = 'INDEX_INSPECTION_SUCCESS_OBSERVATIONS_BYTE_KEY_SEPARATION_AND_EXACT_VALUES'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'None; first finite source attempt.'
plan['artifact_policy'] = 'One source and bounded receipts/object; complete exact four-module first owned root and exact complete core external floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit protections unchanged.'
plan['invocation'] = 'Autonomous serial narrow inspection/key facts; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'SOURCE_AND_COMPLETE_FOUR_MODULE_OWNED_ROOT_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 16, 'inherited_audits': 59, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
