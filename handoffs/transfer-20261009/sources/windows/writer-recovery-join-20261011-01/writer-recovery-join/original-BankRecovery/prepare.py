"""Fresh exact existing three-module replay; no source or guard changes."""
import hashlib
import importlib.util
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
MAIN = DIAG.parent.parent
PRIOR = DIAG / 'transfer-deferred-queue-model-20261010-03'
POOL = DIAG / 'transfer-readback-recovery-publication-owned-floor-20261010-02'
RUNTIME = Path('C:/src/shieldd-pr160-844389ee')
def pin(path):
    path = Path(path)
    with path.open('rb') as stream:
        sha = hashlib.file_digest(stream, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
assert not (ROOT / 'plan.json').exists() and not POOL.exists()
runner = ROOT / 'execute_bounded.py'
assert pin(PRIOR / runner.name)['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(PRIOR / runner.name, runner)
spec = importlib.util.spec_from_file_location('publication_exact_auditor', runner)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((PRIOR / 'plan.json').read_bytes())
POOL.mkdir()
# This root contains no ShielddSecurity package and cannot shadow the fresh
# project package. Its selected owned import set is genuinely empty.
(POOL / 'modules').mkdir()
composition = {'admission_ready': True, 'kernel_credit': 0, 'objects': 0,
    'selected': [], 'input_records': [], 'inherited_public_reports': [],
    'charged_new_object_bytes': 0,
    'scope': 'Empty owned import floor. All three owned modules are exact source targets compiled in dependency order within the fresh project; no retained object or hidden second-package fallback is admitted.'}
composition_file = POOL / 'composition-review.json'
composition_file.write_bytes((json.dumps(composition, indent=2, sort_keys=True) + '\n').encode())
counts = {'TransferReadback': 17, 'TransferBankRecovery': 10, 'TransferWriterPublication': 8}
targets = []
source_pins = []
for module, count in counts.items():
    source = MAIN / 'circuits/ShielddSecurity' / (module + '.lean')
    text = source.read_text()
    assert 'set_option maxHeartbeats 200000' in text
    assert not re.search(r'\b(?:sorry|admit|axiom)\b', m.code_only(text))
    names = re.findall(r'^#check @([^\n]+)', text, re.M)
    assert len(names) == count and names == re.findall(r'^#print axioms ([^\n]+)', text, re.M)
    theorem_names = re.findall(r'^theorem ([A-Za-z0-9_]+)', m.code_only(text), re.M)
    assert set(names) == set(theorem_names), 'every theorem must be audited'
    target = ROOT / 'project/ShielddSecurity' / source.name
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    assert pin(target)['sha256'] == pin(source)['sha256']
    imports, _ = m.header(text)
    targets.append({'module': module, 'source': pin(target), 'predecessor_source': pin(source),
        'imports': imports, 'audit_names': ['ShielddSecurity.' + module + '.' + n for n in names]})
    source_pins += [pin(source), pin(target)]
runtime_paths = ['crates/core/app/src/app/host.rs',
    'crates/core/component/sct/src/permanent_nullifiers.rs',
    'crates/core/component/sct/src/permanent_nullifiers/store.rs']
runtime_sources = [pin(RUNTIME / relative) for relative in runtime_paths]
mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': runtime_sources,
    'readback': 'A successful status checks store readiness/health, the requested full boundary, all sixteen roots and the supplied abstract proof verifier. Pending-or-durable membership uses a successful durable status; unavailable does not mean unspent.',
    'recovery': 'Recovery checks observed roots, intent and retained history before a ready boundary. Fallible primitive I/O outcomes and hash/proof identities remain explicit inputs.',
    'publication': 'The latest application snapshot is independently observed and checked against the ready store boundary and expected height/root/block identity. Capacity failure after Ready is modeled explicitly and cannot be interpreted as no durable progress.',
    'host': 'The model hostIdle function reflects a returned success only. The concrete Host commit phase transition and later application-root presence check remain separate source interfaces; this model does not identify every writer Ready state with concrete Host Idle.',
    'runtime_evidence': {'accepted_packet': pin(DIAG / 'transfer-runtime-completion-packet-20261010-01/manifest.json'),
        'scope': 'Previously accepted finite reader/store/Host controls supply runtime evidence. No new native test is launched by this proof replay; the additional committed-intent native recovery control remains open.'},
    'scope': 'Exact existing symbolic models, not a new runtime implementation. Hashes establish source identity only. Rust ownership/locks/clone/codec, SHA and NOMT semantics, native decoding and complete participating-store durability refinement remain explicit interfaces. These thirty-five public theorem audits do not certify the full Transfer claim.'}
mapping_file = ROOT / 'source-mapping.json'
mapping_file.write_bytes((json.dumps(mapping, indent=2, sort_keys=True) + '\n').encode())
plan['owned_import_pool'] = pin(composition_file)
plan['owned_imports'] = []
plan['lean_path'] = [str(POOL / 'modules'), str(ROOT / 'project')] + plan['lean_path'][2:]
plan['targets'] = targets
baseline = json.loads(Path(plan['preservation']['path']).read_bytes())
plan['pins'] = source_pins + runtime_sources + baseline['protected'] + baseline['foreign']
plan['pins'] += [pin(p) for p in [Path(__file__), runner, composition_file, mapping_file, PRIOR / 'plan.json']]
plan['pins'] += [plan['lean'], plan['external_floor'], plan['preservation'], mapping['runtime_evidence']['accepted_packet']]
unique = {}
for record in plan['pins']:
    key = str(Path(record['path']).resolve()).casefold()
    assert key not in unique or unique[key] == record
    unique[key] = record
plan['pins'] = list(unique.values())
for name in ['deferred', 'future_queue', 'retained_failed_doubling_history', 'retained_failed_history',
    'retained_failed_no16_history', 'retained_failed_witness_history']:
    plan[name] = []
plan['predecessor'] = {'runner_plan_template': pin(PRIOR / 'plan.json')}
plan['kind'] = 'NARROW_EXISTING_READBACK_RECOVERY_WRITER_PUBLICATION_MODEL_REPLAY'
plan['scope'] = mapping['scope']
plan['source_repairs'] = 'None. All three source files are copied byte for byte from the preserved handwritten sources.'
plan['artifact_policy'] = 'Three exact sources and bounded receipts/objects; empty owned floor and complete reachable Lean/Init core external closure.'
plan['repairs'] = 'None. Existing physical, time, heartbeat, thread, process, lint, byte and audit guards unchanged.'
plan['invocation'] = 'Self-reviewed serial narrow replay; exact plan SHA required. Run only after the native wrapper releases the physical-host mutex.'
target = ROOT / 'plan.json'
target.write_bytes((json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n').encode())
review = {'status': 'EXACT_EXISTING_SOURCES_AND_UNCHANGED_GUARDS_SELF_REVIEWED_UNRUN',
    'plan': pin(target), 'runner': pin(runner), 'owned_floor': pin(composition_file),
    'new_source_changes': 0, 'modules': 3, 'public_theorem_audits': 35,
    'native_credit': 0, 'certification': False, 'scope': mapping['scope']}
(ROOT / 'review.json').write_bytes((json.dumps(review, indent=2, sort_keys=True) + '\n').encode())
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6 * 8388608 + 1048576 + 262144 < 134217728
print(json.dumps(review))
