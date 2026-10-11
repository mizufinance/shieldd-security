"""Prepare overlay-derived current volume refusal on the complete qualified closure."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
UPSTREAM = DIAG / 'transfer-ordinary-storage-source-20261011-02'
POOL = DIAG / 'transfer-bound-ordinary-owned-floor-20261011-02'
MODULE = 'TransferBoundOrdinarySource01'

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
stdout = UPSTREAM / 'runs/01-TransferOrdinaryStorageSource01/stdout.txt'
current = m.audit(stdout.read_text(), target['audit_names'])
assert len(current) == 12 and current == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
assert set(audits).isdisjoint(current)
audits.update(current)
records.append(('TransferOrdinaryStorageSource01', target['source'], events[-1]['result']['objects'][0]))
inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferOrdinaryStorageSource01.lean', 'project/ShielddSecurity/TransferOrdinaryStorageSource01.lean']]
inputs.append(pin(stdout))
assert len(records) == 10 and len(audits) == 138
equality = DIAG / 'transfer-verification-equality-source-20261011-02'
eq_plan = json.loads((equality / 'plan.json').read_bytes())
eq_pool = json.loads(Path(eq_plan['owned_import_pool']['path']).read_bytes())
eq_events = [json.loads(s) for s in (equality / 'events.jsonl').read_text().splitlines()]
assert len(eq_events) == 2 and eq_events[-1]['result']['status'] == 'passed'
eq_target = eq_plan['targets'][0]
eq_stdout = equality / 'runs/01-TransferVerificationEqualitySource01/stdout.txt'
eq_reports = m.audit(eq_stdout.read_text(), eq_target['audit_names'])
assert len(eq_reports) == 13 and eq_reports == eq_events[-1]['result']['audits']
assert pin(eq_stdout) == eq_events[-1]['result']['stdout']
for row in eq_pool['selected'] + [{'module': 'TransferVerificationEqualitySource01', 'source': eq_target['source'], 'object': eq_events[-1]['result']['objects'][0]}]:
    old = next((r for r in records if r[0] == row['module']), None)
    if old:
        assert old == (row['module'], row['source'], row['object'])
    else:
        records.append((row['module'], row['source'], row['object']))
for name, report in {**eq_pool['inherited_public_reports'], **eq_reports}.items():
    assert name not in audits or audits[name] == report
    audits[name] = report
inputs += eq_pool['input_records']
inputs += [pin(equality / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferVerificationEqualitySource01.lean', 'project/ShielddSecurity/TransferVerificationEqualitySource01.lean']]
inputs.append(pin(eq_stdout))
assert len(records) == 12 and len(audits) == 162
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
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 12, 'selected': selected,
    'input_records': inputs, 'inherited_public_reports': audits,
    'charged_new_object_bytes': sum(r['copy']['bytes'] for r in selected),
    'scope': 'Complete twelve-module first owned root; 162 inherited full reports; shared five-module raw ancestry verified once. Exact copied objects add no new replay or Rust refinement.'}
composition_file = POOL / 'composition-review.json'
dump(composition_file, composition)
handwritten = ROOT / 'handwritten' / (MODULE + '.lean')
source = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 12 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', source, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(source))
target_source = ROOT / 'project/ShielddSecurity' / handwritten.name
target_source.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target_source)
runtime = Path('C:/src/shieldd-pr160-844389ee')
mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / n) for n in ['crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
        'crates/crypto/proof-params/src/pari.rs', 'crates/core/component/shielded-pool/src/component/shielded_pool.rs',
        'third_party/cnidarium-0.83.0/src/delta.rs']],
    'interfaces': ['Ordinary token is explicit; actual stateless extractor, state/proof validation and registry gate provenance remain upstream',
        'Item statement denotes compared scalar value, envelope denotes serialized bytes; neither implies preimage semantic truth or cryptographic validity',
        'ensure_binds does not inspect registry_id; registry provenance is a separate enclosing gate',
        'Current overlay read availability/key/store correspondence and immutable successfully loaded SCT/tree/CloneCOW/codecs remain inherited',
        'Returned-result child discard is modeled; Rust panic, Host retry/publication and participating-store durability remain separate',
        'No native tests or semantic negative controls and no full Transfer certificate'],
    'scope': 'Whole Ordinary body performs stateless re-extraction and complete Item equality before both installed SCT/pending payload callbacks. Any returned result preserves input nonverifiable writes; family/scalar/envelope mismatch stops before every raw effect. Whole success derives exact re-extraction, initial current-overlay absence, both marker writes and visible marker values under explicit key separation. Existing current or parent entry prevents successful body/delivery and preserves original parent/queue without desired match, reshape, spent-read or rollback premises. Token/extractor/cryptographic/Rust/tree/store/native/durability interfaces and full Transfer remain open.'}
mapping_file = ROOT / 'source-mapping.json'
dump(mapping_file, mapping)
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = [r['copy'] for r in selected]
plan['lean_path'][0:2] = [str(POOL / 'modules'), str(ROOT / 'project')]
plan['targets'] = [{'module': MODULE, 'source': pin(target_source), 'predecessor_source': pin(handwritten),
    'imports': ['ShielddSecurity.TransferOrdinaryStorageSource01', 'ShielddSecurity.TransferVerificationEqualitySource01'],
    'audit_names': ['ShielddSecurity.' + MODULE + '.' + n for n in names]}]
baseline = json.loads(Path(plan['preservation']['path']).read_bytes())
plan['pins'] = baseline['protected'] + baseline['foreign'] + inputs + plan['owned_imports']
plan['pins'] += [pin(p) for p in [Path(__file__), ROOT / 'prepare_successor.py', runner, handwritten, target_source, composition_file, mapping_file]]
plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'EXACT_ITEM_REEXTRACTION_JOINS_ORDINARY_STORAGE_AND_DELIVERY_SOURCE'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh02 unfolds executeBound at one existing-entry refusal rewrite before applying the exact rebinding lemma. Two program definitions and ten theorem contracts unchanged. Failed01 whole zero credit; exact common raw source/object/audit ancestry, guards and strict audits unchanged.'
plan['artifact_policy'] = 'One source and bounded reports/object; complete twelve-module owned root and reachable core floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit guards unchanged.'
plan['invocation'] = 'Autonomous serial narrow current-volume overlay source proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'BOUND_ORDINARY_AND_COMPLETE_TWELVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'fresh_audits': 12, 'inherited_audits': 162, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
dump(ROOT / 'review.json', review)
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
