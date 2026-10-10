"""Seal two new join sources and distinguish newly checked results from retained imports."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
def pin(path):
    path=Path(path)
    with path.open('rb') as f: sha=hashlib.file_digest(f,'sha256').hexdigest()
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':sha}
packet=ROOT/'packet'; packet.mkdir(exist_ok=False)
def copy(path,relative):
    path=Path(path); dest=packet/relative
    dest.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(path,dest)
    assert pin(path)['sha256']==pin(dest)['sha256']
entries=[]
for name in ['transfer-concrete-cardinality-join-20261010-01','transfer-concrete-closed-cardinality-20261010-01']:
    task=DIAG/name; plan=json.loads((task/'plan.json').read_text())
    done=[json.loads(x) for x in (task/'events.jsonl').read_text().splitlines() if json.loads(x)['event']=='attempt_finished']
    assert len(done)==len(plan['targets'])==1 and done[0]['result']['status']=='passed'
    for file in ['plan.json','events.jsonl','prepare.py','execute_bounded.py','review.json']:
        copy(task/file,'tasks/'+name+'/'+file)
    if (task/'prepare_recipe.py').exists(): copy(task/'prepare_recipe.py','recipes/'+name+'-prepare_recipe.py')
    e=done[0]; target=plan['targets'][0]; result=e['result']
    for r in [target['source'],result['stdout']]+result['objects']: assert pin(r['path'])==r
    assert len(result['audits'])==len(target['audit_names'])
    assert all(set(a['axioms']) <= {'propext','Classical.choice','Quot.sound'} for a in result['audits'].values())
    copy(target['source']['path'],'handwritten-source/ShielddSecurity/'+e['module']+'.lean')
    copy(result['stdout']['path'],'audit-output/'+e['module']+'.txt')
    entries.append({'module':e['module'],'source':target['source'],'audit_pairs':len(result['audits']),'task':name,'scope':plan['scope'],'receipt':result})
assert len(entries)==2 and sum(e['audit_pairs'] for e in entries)==6
old=DIAG/'transfer-implementation-20261002/windows-point-order-20261009-01-kernel'
for name in ['ConcreteJubjubField01','ConcreteEdwardsParameters01','ConcreteWeierstrassPoint01',
    'ConcretePointOperationPilot01','ConcretePointTraceComposition01','ConcretePointOrder01']:
    copy(old/'project/ShielddSecurity'/(name+'.lean'),'retained-import-context/ShielddSecurity/'+name+'.lean')
copy(old/'manifest.json','receipts/retained-base-order-manifest.json')
copy(old/'ConcretePointOrder01/audit.json','receipts/retained-base-order-audit.json')
copy(old/'complete.txt','receipts/retained-base-order-complete.txt')
copy(old/'exit.txt','receipts/retained-base-order-exit.txt')
for name in ['transfer-base-order-import-review-20261010-01','transfer-base-order-shared-source-review-20261010-02',
    'transfer-base-order-canonical-source-review-20261010-01']:
    copy(DIAG/name/'review.json','receipts/'+name+'.json')
    copy(DIAG/name/'inspect.py','recipes/'+name+'-inspect.py')
    if (DIAG/name/'prepare.py').exists(): copy(DIAG/name/'prepare.py','recipes/'+name+'-prepare.py')
canonical=json.loads((DIAG/'transfer-base-order-canonical-source-review-20261010-01/review.json').read_text())
assert canonical['all_match'] and len(canonical['modules'])==362
pool=DIAG/'transfer-base-order-owned-floor-20261010-02'
pool_review=json.loads((pool/'composition-review.json').read_text())
assert pool_review['admission_ready'] and pool_review['kernel_credit']==0
assert sum(p.stat().st_size for p in pool.rglob('*') if p.is_file())==66713365 <64*1024**2
copy(pool/'composition-review.json','receipts/owned-package-composition.json')
copy(pool/'prepare.py','recipes/owned-package-composition-prepare.py')
failed=DIAG/'transfer-base-order-owned-floor-20261010-01'
rejected_bytes=sum(p.stat().st_size for p in failed.rglob('*') if p.is_file())
assert rejected_bytes==67253868 >=64*1024**2
copy(failed/'composition-review.json','retained-rejected-composition/composition-review.json')
copy(failed/'prepare.py','retained-rejected-composition/prepare.py')
(packet/'retained-rejected-composition/classification.json').write_text(json.dumps({
    'observed_task_bytes':rejected_bytes,'cap_bytes':64*1024**2,'status':'REJECTED_FINAL_ALL_ARTIFACT_GUARD',
    'kernel_credit':0,'admission_credit':0,'verifier_launched':False,
    'scope':'The first recipe wrote provisional admission_ready metadata before its final guard rejected duplicate metadata. That provisional value is never accepted; only fresh02 independently admitted. Original failed artifacts remain unchanged. No semantic negative-control credit.'},indent=2)+'\n')
check=DIAG/'transfer-closed-cardinality-checkpoint-20261010-01'
copy(check/'preservation.json','receipts/preservation.json')
copy(check/'preservation_check.py','recipes/preservation_check.py')
parent=DIAG/'transfer-eight-torsion-endpoint-20261010-01'
copy(parent/'packet/manifest.json','inputs/eight-torsion-parent-manifest.json')
(packet/'receipts/qualified-new-modules.json').write_text(json.dumps(entries,indent=2)+'\n')
copy(Path(__file__),'recipes/assemble.py')
files=[]
for path in sorted(packet.rglob('*')):
    if path.is_file():
        r=pin(path); r['path']=path.relative_to(packet).as_posix(); files.append(r)
manifest={'kind':'SCOPED_WINDOWS_CLOSED_ACTUAL_CURVE_CARDINALITY_AND_GLOBAL_EXPONENT',
    'files':files,'source_files':2,'retained_import_context_sources':6,'type_axiom_pairs':6,
    'modules':[{'module':e['module'],'source_sha256':e['source']['sha256'],'audit_pairs':e['audit_pairs']} for e in entries],
    'parent_archive':pin(parent/'portable-windows-eight-torsion-endpoint01.tar.xz'),
    'canonical_parent_sha':'2094aed7c6ac14a54ffdd205f5daefb5a18f8a01',
    'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
    'allowed_axioms':['propext','Classical.choice','Quot.sound'],
    'proof':'Two conditional actual joins retain only exact base order. A separately newly checked closed join binds the previously traced concrete base definitionally to the actual curve, establishes its exact orderr, then proves Nat.card curve.Point=8r and8r annihilates every actual point with no cardinality/base-order premise.',
    'retained_import_scope':'Old362 declaration bodies equal maintained canonical bodies; shared42 equal separately passed current prerequisite bodies. Complete current external floor pinned;383 owned objects explicitly copied under a separately charged66713365-byte task. Historical modules are retained imports, not claimed newly replayed. Hash identities are separate from the source body checks and fresh theorem audits. Six context sources help inspect exact field/curve/base binding.',
    'runner_change':'Only own_cache separates immutable explicitly selected owned pool from new task artifacts. Exact pool/plan and new target keysets, hashes, no links/escapes, first-package resolution, before/after checks, conservative output reservation and all finite byte/time/memory caps remain enforced.',
    'limits':{'threads':1,'heap_mib':1536,'heartbeats_at_most':300000,'recursion':4096,'task_all_bytes':64*1024**2},
    'complete_curve_cardinality':'PROVED_FOR_ACTUAL_CONCRETE_MATHLIB_CURVE',
    'global_curve_exponent':'PROVED_FOR_ACTUAL_CONCRETE_MATHLIB_CURVE',
    'open_obligations':['Full native representation/admission correspondence','Native durable commit/error/recovery correspondence','All original Transfer rows/copy conditions','Full Transfer'],
    'runtime_credit':0,'negative_control_credit':0,'certification_refresh':False,'native_correspondence':'OPEN','full_transfer':'OPEN','push_owner':'parent'}
(packet/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
archive=ROOT/'portable-windows-closed-cardinality-endpoint01.tar.xz'
with tarfile.open(archive,'w:xz',preset=9) as tar:
    for path in sorted(packet.rglob('*')):
        if not path.is_file(): continue
        data=path.read_bytes(); info=tarfile.TarInfo(path.relative_to(packet).as_posix())
        info.size=len(data); info.mtime=0; info.mode=0o644; tar.addfile(info,io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())<64*1024**2
print(json.dumps({'archive':pin(archive),'manifest':pin(packet/'manifest.json'),'files':len(files)+1,'source_files':2,'type_axiom_pairs':6}))
