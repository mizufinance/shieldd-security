"""Seal18scoped sources/92audits; preserve every rejected predecessor's zero credit."""
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import tarfile

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
STAGES = [('transfer-concrete-admission-model-20261010-01', 1),
          ('transfer-sdk-extended-model-20261010-03', 1),
          ('transfer-sdk-concrete-model-20261010-01', 1),
          ('transfer-sdk-multiply-model-20261010-03', 1),
          ('transfer-sdk-admission-model-20261010-05', 1),
          ('transfer-sdk-spend-auth-certificates-20261010-01', 1),
          ('transfer-sdk-spend-auth-join-20261010-02', 1)]

def pin(path):
    path = Path(path)
    with path.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
entries = []; phases = []
for task_name, count in STAGES:
    task = DIAG / task_name
    plan = json.loads((task / 'plan.json').read_text())
    events = [json.loads(line) for line in (task / 'events.jsonl').read_text().splitlines()]
    completed = [e for e in events if e['event'] == 'attempt_finished']
    passes = [e for e in completed if e['result']['status'] == 'passed']
    assert len(passes) == count
    for e in passes:
        target = next(t for t in plan['targets'] if t['module'] == e['module'])
        result = e['result']
        for r in [target['source'], result['stdout']] + result['objects']:
            assert pin(r['path']) == r
        assert list(result['audits']) == sorted(target['audit_names'])
        assert len(result['audits']) == len(target['audit_names'])
        assert all(set(a['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in result['audits'].values())
        text = Path(result['stdout']['path']).read_bytes().decode('utf-8')
        assert not re.search(r'\b(?:error|warning|info|trace):|\bsorryAx\b', text)
        audits = []
        for name in target['audit_names']:
            pattern = r"(?m)^@?" + re.escape(name) + r"\s*:[\s\S]*?^'" + re.escape(name) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
            matches = list(re.finditer(pattern, text)); assert len(matches) == 1
            signature = matches[0].group(0).split("\n'" + name + "' ", 1)[0]
            assert hashlib.sha256(signature.encode()).hexdigest() == result['audits'][name]['full_type_sha256']
            audits.append({'declaration': name, 'full_type': signature, **result['audits'][name]})
        entries.append({'module': e['module'], 'task': task_name, 'source': target['source'],
                        'audits': audits, 'receipt': result,
                        'source_class': 'generated' if e['module'] in ['SDKSpendAuthCertificates01'] else 'handwritten'})
    phases.append({'task': task_name, 'plan': pin(task / 'plan.json'), 'selected_passes': count,
                   'rejected_attempts': [{'module': e['module'], 'reason': e['result']['reason'], 'credit': 0,
                       'semantic_negative_control_credit': 0} for e in completed if e['result']['status'] != 'passed']})
assert len(entries) == 7 and len({e['module'] for e in entries}) == 7
assert sum(len(e['audits']) for e in entries) == 98
packet = ROOT / 'packet'; packet.mkdir(exist_ok=False)
def copy(path, relative):
    path = Path(path); target = packet / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    assert not target.exists()
    shutil.copyfile(path, target)
    assert pin(target)['sha256'] == pin(path)['sha256']
for e in entries:
    copy(e['source']['path'], e['source_class'] + '-source/ShielddSecurity/' + e['module'] + '.lean')
    target = packet / 'proof-audits' / (e['module'] + '.json')
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps({'module': e['module'], 'audits': e['audits'],
                                 'captured_stdout': e['receipt']['stdout'], 'receipt': e['receipt']}, indent=2) + '\n')
for task_name, _ in STAGES:
    task = DIAG / task_name
    for name in ['prepare.py', 'prepare_recipe.py', 'plan.json', 'review.json', 'events.jsonl', 'execute_bounded.py']:
        if (task / name).exists():
            copy(task / name, 'execution-context/' + task_name + '/' + name)

rejected = []
for task_name, classification, module in [
    ('transfer-sdk-extended-model-20261010-01', 'Missing extensionality theorem: compiler rejection', 'SDKJubjubExtended01'),
    ('transfer-sdk-extended-model-20261010-02', 'Lean interpreter memory threshold rejection: no object acceptance', 'SDKJubjubExtended01'),
    ('transfer-sdk-multiply-model-20261010-01', 'Local notation field projection resolution failure: compiler rejection', 'SDKJubjubMultiply01'),
    ('transfer-sdk-multiply-model-20261010-02', 'Byte-reader goal rewrite mismatch: compiler rejection', 'SDKJubjubMultiply01'),
    ('transfer-sdk-admission-model-20261010-01', 'Concrete addition inference heartbeat rejection', 'SDKSubgroupAdmission01'),
    ('transfer-sdk-admission-model-20261010-02', 'Explicit concrete addition elaboration heartbeat rejection', 'SDKSubgroupAdmission01'),
    ('transfer-sdk-admission-model-20261010-03', 'Affine proof application elaboration heartbeat rejection', 'SDKSubgroupAdmission01'),
    ('transfer-sdk-admission-model-20261010-04', 'Opaque fold exposed canonical reader mismatch: compiler rejection', 'SDKSubgroupAdmission01')]:
    task = DIAG / task_name
    records = [pin(task / name) for name in ['plan.json', 'review.json', 'events.jsonl', 'execute_bounded.py', 'handwritten/' + module + '.lean', 'runs/01-' + module + '/stdout.txt']]
    rejected.append({'task': task_name, 'classification': classification, 'immutable_records': records,
                     'rejected_attempt_credit': 0, 'semantic_negative_control_credit': 0})
(packet / 'receipts').mkdir()
(packet / 'receipts/rejected-attempts.json').write_text(json.dumps(rejected, indent=2) + '\n')
(packet / 'receipts/qualified-phases.json').write_text(json.dumps(phases, indent=2) + '\n')
for name in ['transfer-concrete-admission-owned-floor-20261010-01', 'transfer-sdk-concrete-owned-floor-20261010-01', 'transfer-sdk-multiply-owned-floor-20261010-01', 'transfer-sdk-admission-owned-floor-20261010-01', 'transfer-sdk-spend-auth-owned-floor-20261010-01']:
    task = DIAG / name
    for filename in ['prepare.py', 'prepare_recipe.py', 'composition-review.json']:
        copy(task / filename, 'owned-import-context/' + name + '/' + filename)
source = DIAG / 'transfer-sdk-source-binding-20261010-01'
for filename in ['fetch.py', 'source-identities.json']:
    copy(source / filename, 'source-provenance/' + filename)
for relative in ['jubjub-0.10.0/src/lib.rs', 'reddsa-0.5.2/src/verification_key.rs', 'reddsa-0.5.2/src/constants.rs', 'reddsa-0.5.2/src/lib.rs']:
    copy(source / 'sources' / relative, 'source-provenance/pinned-sdk/' + relative)
check = DIAG / 'transfer-sdk-admission-checkpoint-20261010-02'
for filename in ['preservation.json', 'preservation_check.py']:
    copy(check / filename, 'receipts/' + filename)
parent = DIAG / 'transfer-concrete-cofactor-endpoint-20261010-01'
copy(parent / 'packet/manifest.json', 'inputs/concrete-cofactor-parent-manifest.json')
for filename in ['split_recipe.py']:
    copy(DIAG / 'transfer-sdk-extended-model-20261010-03' / filename, 'recipes/' + filename)
copy(Path(__file__), 'recipes/assemble.py')
copy(ROOT / 'prepare_assembly.py', 'recipes/prepare_assembly.py')
copy(DIAG / 'transfer-sdk-multiply-model-20261010-03/repair_recipe.py', 'recipes/scalar-loop-repair.py')
copy(DIAG / 'transfer-sdk-admission-model-20261010-05/repair_recipe.py', 'recipes/admission-inference-repair.py')
copy(DIAG / 'transfer-sdk-spend-auth-join-20261010-02/prepare_fresh.py', 'recipes/base-join-preparation-recovery.py')
copy(DIAG / 'transfer-sdk-spend-auth-join-20261010-02/preparation-recovery.json', 'receipts/unrun-base-join-preparation-recovery.json')
gen = DIAG / 'transfer-sdk-spend-auth-generation-20261010-01'
portable = DIAG / 'transfer-sdk-spend-auth-generation-20261010-03'
assert (gen / 'generated/SDKSpendAuthCertificates01.lean').read_bytes() == (portable / 'generated/SDKSpendAuthCertificates01.lean').read_bytes()
compiled = next(e for e in entries if e['module'] == 'SDKSpendAuthCertificates01')
assert Path(compiled['source']['path']).read_bytes() == (gen / 'generated/SDKSpendAuthCertificates01.lean').read_bytes()
for relative in ['generate.py', 'prepare_portable.py', 'inputs/proposals.json', 'generation-review.json']:
    copy(portable / relative, 'recipes/portable-sdk-base-generator/' + relative)
for relative in ['generate.py', 'generation-review.json']:
    copy(gen / relative, 'generation-context/qualified/' + relative)
copy(DIAG / 'transfer-sdk-spend-auth-proposal-20261010-01/propose.py', 'generation-context/propose.py')
reproduction = {'qualified':pin(gen / 'generated/SDKSpendAuthCertificates01.lean'), 'portable_regeneration':pin(portable / 'generated/SDKSpendAuthCertificates01.lean'), 'compiled_source':compiled['source'], 'byte_identical':True, 'generation_credit':0}
(packet / 'receipts/generator-reproduction.json').write_text(json.dumps(reproduction,indent=2)+'\n')
files = []
for path in sorted(packet.rglob('*')):
    if path.is_file():
        record = pin(path); record['path'] = path.relative_to(packet).as_posix(); files.append(record)
manifest = {'kind': 'SCOPED_CONCRETE_SUBGROUP_ADMISSION_AND_SDK_ARITHMETIC_MULTIPLY_SOURCE_MODEL',
    'files': files, 'source_files': 7, 'handwritten_sources': 6, 'generated_sources': 1, 'type_axiom_pairs': 98,
    'modules': [{'module': e['module'], 'source_sha256': e['source']['sha256'], 'audit_pairs': len(e['audits']), 'source_class': e['source_class']} for e in entries],
    'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'concrete_cofactor_parent_archive': pin(parent / 'portable-windows-concrete-cofactor-endpoint01.tar.xz'),
    'latest_parent_canonical_sha_at_seal': '6b7bcae41f3adb64a9094c325f88e0eb641bb4bb',
    'scope': 'Independent curve/modulus admission derives the key subgroup premise and authorization cofactor preimage in the closed mathematical model. SDK five-coordinate source formulas collapse to owned complete arithmetic with nonzero Z and split-T integrity; the opposite doubling projective sign is proved. Symbolic reversed binary fold and canonical little-endian integer reader establish multiplication and modulus-test equivalence. The SDK compressed constant has certified mathematical curve coordinates and an independently certified eight-preimage; the closed global exponent proves subgroup membership. SDK-modeled randomization/native cofactor completeness uses this SDK-specific mathematical base without requiring equality to the distinct old traced base. Native Rust field/byte/decoder/iterator representation refinement remains open.',
    'guard_delta': 'No physical guard change. Lean heap1536MiB/j1/finite300000 heartbeats/rec4096/240s per module/600s per task/4GiB Job/pressure/mutex remain unchanged. Arithmetic split after a rejected interpreter memory-limit attempt. Artifact128MiB/object8MiB packaging thresholds inherited from previously reviewed delta.',
    'open_obligations': ['Pinned native SDK SPEND_AUTH decoder/representation corresponds to the certified mathematical coordinates', 'Primitive Rust field, canonical byte and iterator representation refinement', 'Whole Transfer row/copy/native correspondence and final portable replay'],
    'runtime_test_credit': 0, 'bounded_model_check_credit': 0, 'semantic_negative_control_credit': 0,
    'native_source_correspondence_credit': 0, 'full_transfer': 'OPEN', 'certification': False,
    'repository_payload_policy': 'Handwritten proof sources, normalized full type/axiom evidence, plan/runner provenance and SDK source snapshot only. No raw compiler logs, objects, toolchains, caches or composed runtime workspaces.'}
(packet / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
archive = ROOT / 'portable-windows-sdk-admission-endpoint01.tar.xz'
with tarfile.open(archive, 'w:xz', preset=6) as tar:
    for path in sorted(packet.rglob('*')):
        if path.is_file():
            data = path.read_bytes(); info = tarfile.TarInfo(path.relative_to(packet).as_posix())
            info.size = len(data); info.mtime = 0; info.mode = 0o644
            tar.addfile(info, io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 128 * 1024**2
print(json.dumps({'archive': pin(archive), 'manifest': pin(packet / 'manifest.json'), 'sources': 7, 'audits': 98, 'full_transfer': 'OPEN', 'certification': False}))
