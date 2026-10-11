"""Qualify exact three-NV-write framing and join the successful raw delivery model."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PREVIOUS = DIAG / 'transfer-raw-delivery-composition-20261011-02'
POOL = DIAG / 'transfer-index-writer-owned-floor-20261011-01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

assert not (ROOT / 'plan.json').exists() and not POOL.exists()
runner = ROOT / 'execute_bounded.py'
assert pin(PREVIOUS / runner.name)['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(PREVIOUS / runner.name, runner)
spec = importlib.util.spec_from_file_location('index_writer_exact_auditor', runner)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((PREVIOUS / 'plan.json').read_bytes())
existing = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
events = [json.loads(s) for s in (PREVIOUS / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
audits = m.audit((PREVIOUS / 'runs/01-TransferRawDeliveryComposition01/stdout.txt').read_text(), plan['targets'][0]['audit_names'])
assert len(audits) == 5 and audits == events[-1]['result']['audits']
selected = []
POOL.mkdir()
inputs = existing['input_records'] + [pin(PREVIOUS / name) for name in [
    'plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferRawDeliveryComposition01.lean', 'project/ShielddSecurity/TransferRawDeliveryComposition01.lean',
    'runs/01-TransferRawDeliveryComposition01/stdout.txt']]
records = [(r['module'], r['source'], r['object']) for r in existing['selected']]
records += [('TransferRawDeliveryComposition01', plan['targets'][0]['source'], events[-1]['result']['objects'][0])]
for module, source, obj in records:
    assert pin(source['path']) == source and pin(obj['path']) == obj
    copy = POOL / 'modules/ShielddSecurity' / (module + '.olean')
    copy.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(obj['path'], copy)
    assert pin(copy)['sha256'] == obj['sha256']
    selected.append({'module': module, 'source': source, 'object': obj, 'copy': pin(copy)})
    inputs += [source, obj]
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 3, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': {**existing['inherited_public_reports'], **audits},
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete exact first owned package for the three-module closure: accepted cache, raw failure-aware program and qualified raw success composition. Thirty-three full inherited declaration types and standard axioms checked. Exact object copies are not new replay or Rust correspondence.'}
composition_file = POOL / 'composition-review.json'
composition_file.write_bytes((json.dumps(composition, indent=2, sort_keys=True) + '\n').encode())
handwritten = ROOT / 'handwritten/TransferIndexWriterModel01.lean'
source = handwritten.read_text()
names = re.findall(r'^(?:abbrev|inductive|structure|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 26 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', source, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(source))
target = ROOT / 'project/ShielddSecurity' / handwritten.name
target.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target)
runtime = Path('C:/src/shieldd-pr160-844389ee')
mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / name) for name in ['crates/core/app/src/app/mod.rs', 'crates/core/app/src/app/state_key.rs']],
    'order': 'Transaction conversion, duplicate-ID read/check, count read/decode (absent means zero), checked u64 increment, then exactly entry payload / identifier ordinal / next count writes.',
    'primitive': 'putNV changes only one child nonverifiable entry, retaining verifiable/object/event components and all unrelated NV entries. Three-write composition directly derives the same frame and final count entry.',
    'joined_success': 'The actual raw program outcome is recovered from successful PerTx delivery. The installed concrete index callback then derives an observed inspection witness and exact three-write child cache; earlier raw verifiable/object/events and unrelated NV entries survive application to the original parent.',
    'interfaces': ['Transaction conversion/proto encoding and identifier correspondence', 'u64 big-endian decode/encode', 'Nat key projection from exact byte keys; key injectivity and disjointness are not assumed globally', 'Storage reads return explicit read failures or observations; alias/Clone/COW correspondence of the modeled primitive', 'Raw execution primitive commands, concrete state root/readback/durability correspondence'],
    'scope': 'Functional source-order model and compositional proof only. Exact source hashes establish identity, not semantic correspondence. Native index/late-delivery controls remain separate finite evidence, and the three new genuine controls remain unrun. No native or full Transfer certification credit.'}
mapping_file = ROOT / 'source-mapping.json'
mapping_file.write_bytes((json.dumps(mapping, indent=2, sort_keys=True) + '\n').encode())
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': 'TransferIndexWriterModel01', 'source': pin(target),
    'predecessor_source': pin(handwritten), 'imports': ['ShielddSecurity.TransferRawDeliveryComposition01'],
    'audit_names': ['ShielddSecurity.TransferIndexWriterModel01.' + name for name in names]}]
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
plan['kind'] = 'EXACT_THREE_NV_WRITE_SOURCE_ORDER_INDEX_FRAME_AND_RAW_DELIVERY_COMPOSITION'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'None; first source attempt with finite reusable primitive/framing/composition lemmas.'
plan['artifact_policy'] = 'One source and bounded receipts/object; complete exact three-module first owned root; exact complete reachable core external floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit protections unchanged.'
plan['invocation'] = 'Autonomous serial narrow index writer model; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'SOURCE_AND_COMPLETE_THREE_MODULE_OWNED_ROOT_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 26, 'inherited_audits': 33, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
