"""Seal16scoped sources/172audits; preserve every rejected predecessor's zero credit."""
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import tarfile

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
STAGES = [('transfer-sdk-spend-auth-order-20261010-01', 1), ('transfer-sdk-compressed-roundtrip-20261010-01', 1), ('transfer-sdk-program-prerequisites-20261010-01', 2), ('transfer-sdk-owned-programs-20261010-01', 3), ('transfer-sdk-native-spend-auth-20261010-02', 3), ('transfer-sdk-raw-point-multiply-20261010-02', 2), ('transfer-sdk-raw-codec-20261010-01', 2), ('transfer-sdk-raw-authorization-20261010-01', 1), ('transfer-sdk-raw-authorization-join-20261010-02', 1)]

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
assert len(entries) == 16 and len({e['module'] for e in entries}) == 16
assert sum(len(e['audits']) for e in entries) == 172
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
    ('transfer-sdk-native-spend-auth-20261010-01','SDKNativeSpendAuth01','Missing explicit standard coordinate premise and Option-match reduction: compiler rejection'),
    ('transfer-sdk-raw-point-multiply-20261010-01','ShielddNativeReadPoint','Unused checked simp argument: strict warning rejection'),
    ('transfer-sdk-raw-authorization-join-20261010-01','SDKRawAuthorization01','Order lemma selected instead of additive-group negation identity: compiler rejection')]:
    task = DIAG / task_name
    records = [pin(task / name) for name in ['plan.json','review.json','events.jsonl','execute_bounded.py','handwritten/'+module+'.lean','runs/01-'+module+'/stdout.txt'] if (task/name).is_file()]
    assert json.loads((task/'events.jsonl').read_text().splitlines()[-1])['result']['status'] == 'failed'
    rejected.append({'task':task_name,'classification':classification,'immutable_records':records,'rejected_attempt_credit':0,'semantic_negative_control_credit':0})
(packet / 'receipts').mkdir()
(packet / 'receipts/rejected-attempts.json').write_text(json.dumps(rejected,indent=2)+'\n')
(packet / 'receipts/qualified-phases.json').write_text(json.dumps(phases,indent=2)+'\n')
floor = DIAG/'transfer-sdk-raw-authorization-floor-20261010-01'
for name in ['prepare.py','prepare_recipe.py','composition-review.json']:
    copy(floor/name,'owned-import-context/'+name)
for task_name,_ in STAGES:
    copied_names = {'prepare.py','prepare_recipe.py','plan.json','review.json','events.jsonl','execute_bounded.py'}
    for path in sorted((DIAG/task_name).iterdir()):
        if path.is_file() and ((path.suffix == '.py' and path.name not in copied_names) or path.name == 'source-review.json'):
            copy(path,'execution-context/'+task_name+'/'+path.name)
    review_path = DIAG/task_name/'source-review.json'
    if review_path.exists():
        for record in json.loads(review_path.read_text()):
            if 'prior_handwritten' in record:
                module = record['module']
                relative = 'inputs/prior-handwritten/'+module+'.lean'
                if not (packet/relative).exists():
                    copy(record['prior_handwritten']['path'],relative)
for layer in ['transfer-sdk-native-witness-owned-floor-20261010-02',
              'transfer-sdk-program-owned-floor-20261010-01',
              'transfer-sdk-owned-program-floor-20261010-01',
              'transfer-sdk-native-spend-auth-floor-20261010-02',
              'transfer-sdk-raw-point-multiply-floor-20261010-01',
              'transfer-sdk-raw-codec-floor-20261010-01']:
    for path in sorted((DIAG/layer).iterdir()):
        if path.is_file() and (path.suffix == '.py' or path.name == 'composition-review.json'):
            copy(path,'owned-import-context/'+layer+'/'+path.name)
for layer in ['transfer-sdk-raw-route-refresh-20261010-01','transfer-sdk-raw-route-refresh-20261010-02']:
    copy(DIAG/layer/'prepare.py','recipes/'+layer+'/prepare.py')
check = DIAG/'transfer-sdk-raw-authorization-checkpoint-20261010-01'
for name in ['preservation.json','preservation_check.py','prepare.py']:
    copy(check/name,'receipts/'+name)
parent = DIAG/'transfer-sdk-compressed-admission-endpoint-20261010-01'
copy(parent/'packet/manifest.json','inputs/sdk-compressed-admission-parent-manifest.json')
source = DIAG/'transfer-sdk-source-binding-20261010-01'
copy(source/'source-identities.json','source-provenance/source-identities.json')
copy(source/'sources/jubjub-0.10.0/src/lib.rs','source-provenance/pinned-sdk/jubjub-0.10.0/src/lib.rs')
runtime_context = json.loads((ROOT/'runtime-context.json').read_text())
assert runtime_context['runtime_sha'] == '844389ee069e1fb2e576708842d0b389b4d9a44a'
assert runtime_context['semantic_correspondence_credit'] == 0
for record in runtime_context['files']:
    path = ROOT/'runtime-context'/record['relative_path']
    assert pin(path)['sha256'] == record['sha256'] and pin(path)['bytes'] == record['bytes']
    copy(path,'source-provenance/runtime/'+record['relative_path'])
copy(ROOT/'runtime-context.json','source-provenance/runtime-context.json')
copy(ROOT/'prepare_runtime_context.py','recipes/prepare_runtime_context.py')
copy(Path(__file__),'recipes/assemble.py')
copy(ROOT/'prepare_assembly.py','recipes/prepare_assembly.py')
copy(ROOT/'selection.json','recipes/selection.json')
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
manifest={'kind':'SCOPED_CONCRETE_SDK_RAW_AUTHORIZATION_ENDPOINT',
    'files':files,'source_files':16,'handwritten_sources':16,'generated_sources':0,'type_axiom_pairs':172,
    'modules':[{'module':e['module'],'source_sha256':e['source']['sha256'],'audit_pairs':len(e['audits']),'source_class':e['source_class']} for e in entries],
    'allowed_axioms':['propext','Classical.choice','Quot.sound'],
    'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
    'sdk_compressed_admission_parent_archive':pin(parent/'portable-windows-sdk-compressed-admission-endpoint01.tar.xz'),
    'latest_parent_canonical_sha_at_seal':'cb017c0e77791e5b12fb3e386b0ced9165374d76',
    'scope':'Independent SDK base has certified exact prime order; full-curve compressed roundtrip includes zero roots and torsion. Globally coordinate-bound standard SpendAuth identifies that base, deriving exact order and actual owned scalar-one reader result without an exact-order premise. Owned raw Scalar/reader/private scalar/encoder/Point/authorization source programs compose with production SDK randomization and admitted output supplies all six native witness arithmetic constraints. Global byte-array encoding meaning derives SDK injectivity/coherence and identifies mathematical admitted key subgroup/nonidentity without an abstract decoder subgroup law. A concrete admitted nonidentity key cancels to identity with scalar one, demonstrating the separate output gate. All remaining Rust/FFI primitive/byte/coordinate correspondence contracts and original circuit rows/copies/final Transfer replay are explicit OPEN obligations.',
    'guard_delta':'No physical or packaging guard changes. Nine runner bodies byte-identical to accepted baseline. Lean heap1536MiB/j1/finite300000 heartbeats/rec4096/240s per module/600s per task/4GiB Job/free-memory/commit/disk-pressure/mutex retained.',
    'open_obligations':['Actual Rust iterator/field/canonical-byte/strict decoder/sqrt/sign representation correspondence','Whole Transfer row/copy/native correspondence and final portable replay'],
    'runtime_test_credit':0,'bounded_model_check_credit':0,'semantic_negative_control_credit':0,'native_source_correspondence_credit':0,
    'full_transfer':'OPEN','certification':False,
    'repository_payload_policy':'Handwritten sources, normalized complete type/axiom reports, immutable plan/runner/provenance and reviewed SDK snapshot. No raw compiler logs, objects, toolchains, caches or composed runtime workspaces.'}
(packet/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
archive=ROOT/'portable-windows-sdk-raw-authorization-endpoint01.tar.xz'
with tarfile.open(archive,'w:xz',preset=6) as tar:
    for path in sorted(packet.rglob('*')):
        if path.is_file():
            data=path.read_bytes(); info=tarfile.TarInfo(path.relative_to(packet).as_posix()); info.size=len(data); info.mtime=0; info.mode=0o644
            tar.addfile(info,io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 128*1024**2
print(json.dumps({'archive':pin(archive),'manifest':pin(packet/'manifest.json'),'sources':16,'audits':172,'full_transfer':'OPEN','certification':False}))
