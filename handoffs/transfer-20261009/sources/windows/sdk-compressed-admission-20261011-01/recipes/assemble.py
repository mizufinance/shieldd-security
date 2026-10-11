"""Seal4scoped sources/27audits; preserve every rejected predecessor's zero credit."""
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import tarfile

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
STAGES = [('transfer-sdk-encoding-injective-model-20261010-02', 1),
          ('transfer-sdk-native-nonidentity-20261010-02', 1),
          ('transfer-sdk-native-witness-20261010-02', 1),
          ('transfer-sdk-compressed-admission-model-20261010-03', 1)]

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
                        'source_class': 'generated' if e['module'] in [] else 'handwritten'})
    phases.append({'task': task_name, 'plan': pin(task / 'plan.json'), 'selected_passes': count,
                   'rejected_attempts': [{'module': e['module'], 'reason': e['result']['reason'], 'credit': 0,
                       'semantic_negative_control_credit': 0} for e in completed if e['result']['status'] != 'passed']})
assert len(entries) == 4 and len({e['module'] for e in entries}) == 4
assert sum(len(e['audits']) for e in entries) == 27
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
for task_name, module, classification in [
    ('transfer-sdk-encoding-injective-model-20261010-01','SDKEncodingInjective01','Missing explicit modulus argument to representative injectivity: compiler rejection'),
    ('transfer-sdk-native-nonidentity-20261010-01','GroupNativeNonidentity','Unused zero_add simplifier argument: strict warning rejection'),
    ('transfer-sdk-compressed-admission-model-20261010-01','SDKCompressedAdmission01','Unqualified native subgroup-witness import: rejected before compilation'),
    ('transfer-sdk-compressed-admission-model-20261010-02','SDKCompressedAdmission01','Reserved public binder name: compiler rejection')]:
    task = DIAG / task_name
    records = [pin(task / name) for name in ['plan.json','review.json','events.jsonl','execute_bounded.py','handwritten/'+module+'.lean','runs/01-'+module+'/stdout.txt'] if (task/name).is_file()]
    assert json.loads((task/'events.jsonl').read_text().splitlines()[-1])['result']['status'] == 'failed'
    rejected.append({'task':task_name,'classification':classification,'immutable_records':records,'rejected_attempt_credit':0,'semantic_negative_control_credit':0})
(packet / 'receipts').mkdir()
(packet / 'receipts/rejected-attempts.json').write_text(json.dumps(rejected,indent=2)+'\n')
(packet / 'receipts/qualified-phases.json').write_text(json.dumps(phases,indent=2)+'\n')
floor = DIAG/'transfer-sdk-native-witness-owned-floor-20261010-02'
for name in ['prepare.py','prepare_recipe.py','composition-review.json']:
    copy(floor/name,'owned-import-context/'+name)
for task_name,_ in STAGES:
    for name in ['prepare_fresh.py','prepare_stage.py','predecessor_prepare_fresh.py','predecessor_prepare_recipe.py']:
        if (DIAG/task_name/name).exists():
            copy(DIAG/task_name/name,'execution-context/'+task_name+'/'+name)
for name in ['GroupNativeNonidentity','GroupNativeSubgroupWitness']:
    copy(Path('C:/src/shieldd-formal/circuits/ShielddSecurity')/(name+'.lean'),'inputs/prior-handwritten/'+name+'.lean')
for layer in ['transfer-sdk-encoding-owned-floor-20261010-01','transfer-sdk-native-nonidentity-owned-floor-20261010-02']:
    for name in ['prepare.py','prepare_recipe.py','composition-review.json']:
        copy(DIAG/layer/name,'owned-import-context/'+layer+'/'+name)
check = DIAG/'transfer-sdk-compressed-admission-checkpoint-20261010-02'
for name in ['preservation.json','preservation_check.py','prepare.py']:
    copy(check/name,'receipts/'+name)
parent = DIAG/'transfer-sdk-codec-endpoint-20261010-01'
copy(parent/'packet/manifest.json','inputs/sdk-codec-parent-manifest.json')
source = DIAG/'transfer-sdk-source-binding-20261010-01'
copy(source/'source-identities.json','source-provenance/source-identities.json')
copy(source/'sources/jubjub-0.10.0/src/lib.rs','source-provenance/pinned-sdk/jubjub-0.10.0/src/lib.rs')
copy(Path(__file__),'recipes/assemble.py')
copy(ROOT/'prepare_assembly.py','recipes/prepare_assembly.py')
runner_checks = []
for task_name,_ in STAGES:
    runner = pin(DIAG/task_name/'execute_bounded.py')
    assert runner['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
    runner_checks.append(runner)
(packet/'receipts/unchanged-runners.json').write_text(json.dumps({'runners':runner_checks,'physical_guard_changes':False,'runtime_credit':0},indent=2)+'\n')
files=[]
for path in sorted(packet.rglob('*')):
    if path.is_file():
        record=pin(path); record['path']=path.relative_to(packet).as_posix(); files.append(record)
manifest={'kind':'SCOPED_MATHEMATICAL_SDK_ENCODING_AND_ADMISSION_NATIVE_CONSTRAINTS',
    'files':files,'source_files':4,'handwritten_sources':4,'generated_sources':0,'type_axiom_pairs':27,
    'modules':[{'module':e['module'],'source_sha256':e['source']['sha256'],'audit_pairs':len(e['audits']),'source_class':e['source_class']} for e in entries],
    'allowed_axioms':['propext','Classical.choice','Quot.sound'],
    'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
    'sdk_codec_parent_archive':pin(parent/'portable-windows-sdk-codec-endpoint01.tar.xz'),
    'latest_parent_canonical_sha_at_seal':'389ba28b9b42012b619ea735a6ddfe8a205ec7df',
    'scope':'Full concrete-curve compressed encoding is injective, including zero roots and torsion. Mathematical curve/encoding/modulus/nonidentity admission identifies a unique actual subgroup nonidentity point and derives all six owned native witness arithmetic constraints. SDK randomization preserves the subgroup and agrees with owned native authorization for canonical scalar casts. A separate randomized-output nonidentity gate is retained. No per-witness target equation, output subgroup, Satisfies or row/copy correspondence is assumed.',
    'guard_delta':'No physical or packaging guard changes. Four runner bodies byte-identical to accepted baseline. Lean heap1536MiB/j1/finite300000 heartbeats/rec4096/240s per module/600s per task/4GiB Job/free-memory/commit/disk-pressure/mutex retained.',
    'open_obligations':['Actual Rust iterator/field/canonical-byte/strict decoder/sqrt/sign representation correspondence','Whole Transfer row/copy/native correspondence and final portable replay'],
    'runtime_test_credit':0,'bounded_model_check_credit':0,'semantic_negative_control_credit':0,'native_source_correspondence_credit':0,
    'full_transfer':'OPEN','certification':False,
    'repository_payload_policy':'Handwritten sources, normalized complete type/axiom reports, immutable plan/runner/provenance and reviewed SDK snapshot. No raw compiler logs, objects, toolchains, caches or composed runtime workspaces.'}
(packet/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
archive=ROOT/'portable-windows-sdk-compressed-admission-endpoint01.tar.xz'
with tarfile.open(archive,'w:xz',preset=6) as tar:
    for path in sorted(packet.rglob('*')):
        if path.is_file():
            data=path.read_bytes(); info=tarfile.TarInfo(path.relative_to(packet).as_posix()); info.size=len(data); info.mtime=0; info.mode=0o644
            tar.addfile(info,io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 128*1024**2
print(json.dumps({'archive':pin(archive),'manifest':pin(packet/'manifest.json'),'sources':4,'audits':27,'full_transfer':'OPEN','certification':False}))
