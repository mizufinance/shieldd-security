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
STAGES = [('transfer-capability-acceptance-20261010-03',1),('transfer-capability-rows-20261010-01',1)]

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
assert len(entries) == 2 and len({e['module'] for e in entries}) == 2
assert sum(len(e['audits']) for e in entries) == 43
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
    ('transfer-capability-acceptance-20261010-01','TransferAcceptance','Unused Prod.fst simp argument: strict warning rejection'),
    ('transfer-capability-acceptance-20261010-02','TransferAcceptance','Pair projection not exposed before slot substitution: compiler rejection')]:
    task = DIAG / task_name
    records = [pin(task / name) for name in ['plan.json','review.json','events.jsonl','execute_bounded.py','handwritten/'+module+'.lean','runs/01-'+module+'/stdout.txt'] if (task/name).is_file()]
    assert json.loads((task/'events.jsonl').read_text().splitlines()[-1])['result']['status'] == 'failed'
    rejected.append({'task':task_name,'classification':classification,'immutable_records':records,'rejected_attempt_credit':0,'semantic_negative_control_credit':0})
(packet / 'receipts').mkdir()
(packet / 'receipts/rejected-attempts.json').write_text(json.dumps(rejected,indent=2)+'\n')
(packet / 'receipts/qualified-phases.json').write_text(json.dumps(phases,indent=2)+'\n')
floor = DIAG/'transfer-capability-owned-floor-20261010-01'
for name in ['prepare.py','prepare_recipe.py','composition-review.json']:
    copy(floor/name,'owned-import-context/'+name)
for task_name,_ in STAGES:
    copied_names={'prepare.py','prepare_recipe.py','plan.json','review.json','events.jsonl','execute_bounded.py'}
    for path in sorted((DIAG/task_name).iterdir()):
        if path.is_file() and ((path.suffix=='.py' and path.name not in copied_names) or path.name in ['source-review.json','runtime-source-identities.json','predecessor_no_family_source.lean.txt']):
            copy(path,'execution-context/'+task_name+'/'+path.name)
copy(DIAG/'transfer-capability-acceptance-20261010-03/source-review.json','source-provenance/acceptance-source-review.json')
copy(Path('C:/src/shieldd-formal/circuits/ShielddSecurity/TransferAcceptance.lean'),'inputs/prior-handwritten/TransferAcceptance.lean')
runtime_context=json.loads((DIAG/'transfer-capability-rows-20261010-01/runtime-source-identities.json').read_text())
for record in runtime_context['files']:
    assert pin(record['copy']['path'])==record['copy']
    copy(record['copy']['path'],'source-provenance/runtime/'+record['runtime_relative_path'])
copy(DIAG/'transfer-sdk-raw-authorization-floor-20261010-01/composition-review.json','owned-import-context/prior432-composition-review.json')
check = DIAG/'transfer-capability-rows-checkpoint-20261010-01'
for name in ['preservation.json','preservation_check.py','prepare.py']:
    copy(check/name,'receipts/'+name)
parent = DIAG/'transfer-sdk-raw-authorization-endpoint-20261010-01'
copy(parent/'packet/manifest.json','inputs/sdk-raw-authorization-parent-manifest.json')
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
manifest={'kind':'CONSTRUCTIVE_TRANSACTION_CAPABILITY_ROW_VALIDATION',
    'files':files,'source_files':2,'handwritten_sources':2,'generated_sources':0,'type_axiom_pairs':43,
    'modules':[{'module':e['module'],'source_sha256':e['source']['sha256'],'audit_pairs':len(e['audits']),'source_class':e['source_class']} for e in entries],
    'allowed_axioms':['propext','Classical.choice','Quot.sound'],
    'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
    'sdk_raw_authorization_parent_archive':pin(parent/'portable-windows-sdk-raw-authorization-endpoint01.tar.xz'),
    'latest_parent_canonical_sha_at_seal':'cb017c0e77791e5b12fb3e386b0ced9165374d76',
    'scope':'Executable slot-map insertion derives unique keys and retains every original capability. Sorted-key comparison derives exact slot coverage; independent registry, ProofLocation family and exact Item checks derive BoundRows for output map and input rows. Mathematical duplicate/wrong-registry/wrong-item rejection is proved; no runtime negative-control credit is asserted. BoundRows and desired coverage/item equations are not premises of constructor success. Original acceptance interface is qualified with one explicit pair-projection change, and both rejected predecessors remain zero-credit. Rust finite maps/ProofSlot ordering/extracted locations/primitive byte-envelope identity, deployed keys, crypto verification and full Transfer circuit/runtime/state/durability joins remain OPEN.',
    'guard_delta':'No physical or packaging guard changes. Two runner bodies byte-identical to accepted baseline. Lean heap1536MiB/j1/finite300000 heartbeats/rec4096/240s per module/600s per task/4GiB Job/free-memory/commit/disk-pressure/mutex retained.',
    'open_obligations':['Rust finite-map and bounded ProofSlot representation/order refinement','Native extracted-location/family and exact canonical byte-envelope correspondence','Deployed-key cryptographic verification and full Transfer circuit/runtime/state/durability joins'],
    'runtime_test_credit':0,'bounded_model_check_credit':0,'semantic_negative_control_credit':0,'native_source_correspondence_credit':0,
    'full_transfer':'OPEN','certification':False,
    'repository_payload_policy':'Handwritten sources, normalized complete type/axiom reports, immutable plan/runner/provenance and reviewed SDK snapshot. No raw compiler logs, objects, toolchains, caches or composed runtime workspaces.'}
(packet/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
archive=ROOT/'portable-windows-capability-rows-endpoint01.tar.xz'
with tarfile.open(archive,'w:xz',preset=6) as tar:
    for path in sorted(packet.rglob('*')):
        if path.is_file():
            data=path.read_bytes(); info=tarfile.TarInfo(path.relative_to(packet).as_posix()); info.size=len(data); info.mtime=0; info.mode=0o644
            tar.addfile(info,io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 128*1024**2
print(json.dumps({'archive':pin(archive),'manifest':pin(packet/'manifest.json'),'sources':2,'audits':43,'full_transfer':'OPEN','certification':False}))
