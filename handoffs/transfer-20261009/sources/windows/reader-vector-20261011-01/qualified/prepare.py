"""Prepare core-only nullifier vector alignment proof with unchanged bounded guard."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PREVIOUS = DIAG / 'transfer-readback-recovery-publication-20261010-02'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

assert not (ROOT / 'plan.json').exists()
runner = ROOT / 'execute_bounded.py'
assert pin(PREVIOUS / runner.name)['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(PREVIOUS / runner.name, runner)
spec = importlib.util.spec_from_file_location('reader_vector_exact_auditor', runner)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((PREVIOUS / 'plan.json').read_bytes())
assert not plan['owned_imports']
assert pin(plan['owned_import_pool']['path']) == plan['owned_import_pool']
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 0 and not pool['selected']
handwritten = ROOT / 'handwritten/TransferNullifierReaderVector01.lean'
source = handwritten.read_text()
names = re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)', m.code_only(source), re.M)
assert len(names) == 13 and re.findall(r'^#check @([^\n]+)', source, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', source, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(source))
target = ROOT / 'project/ShielddSecurity' / handwritten.name
target.parent.mkdir(parents=True)
shutil.copyfile(handwritten, target)
runtime = Path('C:/src/shieldd-pr160-844389ee')
mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / name) for name in ['crates/core/component/sct/src/permanent_nullifiers/store.rs', 'crates/core/component/sct/src/component/tree.rs', 'crates/core/component/sct/src/permanent_nullifiers.rs']],
    'reader': 'Reader.contains captures the boundary and read lock, then iterates every input, obtains status, verifies it against that boundary, and collects one spent flag per successful item. Failure aborts collection. lookupAll is the symbolic recurrence for those verified lookup observations; success derives exact ordered alignment and vector length.',
    'pending': 'contains_nullifiers joins current pending membership into the existing durable vector via in-place zip. joinPending preserves unmatched vector suffixes and proves vector length unchanged even without input-length equality.',
    'stage_check': 'stage_nullifiers zips input nullifiers with contains_nullifiers flags and rejects any spent flag. Reader success plus the pending join derives full alignment; successful zip-unspent therefore implies a verified false durable observation and false pending membership for every input, without an assumed vector length.',
    'interfaces': ['readerGate represents successful boundary/read-lock/object availability preconditions', 'lookup captures an individually status-verified observation at that exact boundary; source/codec/NOMT/Merkle correspondence remains upstream', 'pending is the current Open membership or Sealed ordered membership observation, not a validation snapshot', 'Rust iteration/Vec/zip and snapshot/alias correspondence'],
    'scope': 'Core-only symbolic map/collect, in-place pending zip, length and exhaustive unspent-check proof. Individual status authentication has separate qualified readback evidence; no additional native control or full Transfer certification credit. Source hashes establish identity, not correspondence.'}
mapping_file = ROOT / 'source-mapping.json'
mapping_file.write_bytes((json.dumps(mapping, indent=2, sort_keys=True) + '\n').encode())
plan['lean_path'][1] = str(ROOT / 'project')
plan['targets'] = [{'module': 'TransferNullifierReaderVector01', 'source': pin(target),
    'predecessor_source': pin(handwritten), 'imports': ['Lean'],
    'audit_names': ['ShielddSecurity.TransferNullifierReaderVector01.' + name for name in names]}]
baseline = json.loads(Path(plan['preservation']['path']).read_bytes())
plan['pins'] = baseline['protected'] + baseline['foreign']
plan['pins'] += [pin(p) for p in [Path(__file__), ROOT / 'prepare_successor.py', runner, handwritten, target, mapping_file]]
plan['pins'] += mapping['runtime_sources'] + [plan['lean'], plan['external_floor'], plan['preservation'], plan['owned_import_pool']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'ACTUAL_NULLIFIER_MAP_COLLECT_ALIGNMENT_IN_PLACE_PENDING_ZIP_AND_EXHAUSTIVE_UNSPENT_CHECK'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'Fresh 03 after preserved 01/02 proof-only failures: correct boolean negation lemma, simplify gate branches and remove two tactics after those goals were already closed. Executable definitions and theorem contracts unchanged; rejected attempts zero credit; guards/audits unchanged.'
plan['artifact_policy'] = 'One source and bounded receipts/object, no custom imports and complete core external floor.'
plan['repairs'] = 'All physical/process/thread/time/heartbeat/byte/lint/audit protections unchanged.'
plan['invocation'] = 'Autonomous serial narrow nullifier vector proof; exact plan SHA required.'
plan_file = ROOT / 'plan.json'
plan_file.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'CORE_ONLY_SOURCE_AND_EMPTY_OWNED_IMPORTS_SELF_REVIEWED_UNRUN',
    'plan': pin(plan_file), 'runner': pin(runner), 'owned_floor': plan['owned_import_pool'],
    'fresh_audits': 13, 'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
