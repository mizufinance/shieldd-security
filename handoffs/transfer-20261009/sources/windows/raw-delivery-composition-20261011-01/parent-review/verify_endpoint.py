"""Independent scoped success composition review; no compiler/native execution."""
from pathlib import Path
import json,re,hashlib,ast
J=Path(__file__).parent;P=J/'packet01';W=J.parent.parent;G=W/'shared-build-handoff';A=G/'handoffs/transfer-20261009/sources/windows/raw-state-program-20261011-01';Q=G/'handoffs/transfer-20261009/sources/windows/deferred-queue-20261011-01';OLD=J.parent/'windows-raw-state-review01/packet01'
def read(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
prior=J.parent/'windows-readback-publication-review01/verify_endpoint.py';tree=ast.parse(prior.read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='parse');exec(compile(ast.Module(body=[fn],type_ignores=[]),str(prior),'exec'))
M=read(P/'manifest.json');R=read(P/'review.json');plan=read(P/'qualified/plan.json');pins={}
for e in M['entries']:
 b=(P/e['archive_path']).read_bytes();r=e['original'];assert len(b)==r['bytes']and sha(b)==r['sha256'];pins[r['path']]=r
assert len(M['entries'])==15 and len(plan['targets'])==1
t=plan['targets'][0];b=(P/'source/ShielddSecurity/TransferRawDeliveryComposition01.lean').read_bytes();assert len(b)==t['source']['bytes']and sha(b)==t['source']['sha256'];assert {k:t['source'][k]for k in ['bytes','sha256']}=={k:t['predecessor_source'][k]for k in ['bytes','sha256']}
names=['ShielddSecurity.TransferRawDeliveryComposition01.'+n for n in re.findall(r'^#check @([\w.]+)$',b.decode(),re.M)];assert names==t['audit_names']and len(names)==5
events=[json.loads(l)for l in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(events)==2;result=events[-1]['result'];assert result==R['compiler_result']and result['status']=='passed'
reports=parse(P/'reports/fresh-5-complete-declarations.txt',names,result['audits']);raw=(P/'reports/fresh-5-complete-declarations.txt').read_bytes();assert len(raw)==result['stdout']['bytes']and sha(raw)==result['stdout']['sha256']
assert result['seconds']<240 and result['peak_rss_bytes']<4294967296 and result['command'][1:5]==['-j1','-M1536','-DmaxHeartbeats=300000','-DmaxRecDepth=4096'];assert result['command'][-1]==t['source']['path']and result['command'][-2]==result['objects'][0]['path']
ref=read(P/'context/inherited-reference.json');original=(OLD/'manifest.json').read_bytes();assert len(original)==ref['manifest']['bytes']and sha(original)==ref['manifest']['sha256'];assert original==(A/'manifest.json').read_bytes();assert ref['accepted_evidence_commit']=='ae307b2af3c98242cc6a3be82e5673d89b54f9c4'
inherited=read(A/'parent-review/endpoint-audit-review01.json');audits={e['declaration']:{k:e[k]for k in ['axioms','full_type_sha256']}for e in inherited['full_declarations']+inherited['inherited_declarations']};assert len(audits)==28
owned=read(P/'context/owned-composition-review.json');assert owned['inherited_public_reports']==audits and len(owned['selected'])==2
objects={'TransferStateDelta':inherited['custom_import']['object'],'TransferRawStateProgram01':read(A/'review.json')['compiler_result']['objects'][0]}
for e in owned['selected']:
 n=e['module'];source=(A/'source/ShielddSecurity'/(n+'.lean')).read_bytes();assert len(source)==e['source']['bytes']and sha(source)==e['source']['sha256'];assert {k:e['object'][k]for k in ['bytes','sha256']}=={k:objects[n][k]for k in ['bytes','sha256']};assert {k:e['copy'][k]for k in ['bytes','sha256']}=={k:e['object'][k]for k in ['bytes','sha256']}
assert plan['owned_imports']==[e['copy']for e in owned['selected']];assert t['imports']==['ShielddSecurity.TransferRawStateProgram01']
floor=Q/'context/core-external-floor.json';r=read(A/'context/core-floor-reference.json')['original'];assert len(floor.read_bytes())==r['bytes']and sha(floor.read_bytes())==r['sha256'];assert plan['external_floor']==r
F=read(floor);seen=set();todo=['Lean','Init']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);e=F['modules'][n];todo.extend(e['imports'])
 if e['implicit_Init']:todo.append('Init')
assert len(seen)==2141 and seen==set(F['modules'])and F['gaps']==[]
assert(P/'qualified/execute_bounded.py').read_bytes()==(Q/'qualified/execute_bounded.py').read_bytes()
assert plan['pressure_limits']=={'commit_preflight_mib':1792,'commit_running_mib':512,'free_disk_bytes':2147483648,'one_host_one_heavy':True,'owned_job_memory_and_rss_bytes':4294967296,'physical_preflight_mib':2560,'physical_running_mib':1536}
matched=0
for r in plan['pins']:
 if r['path']in pins:assert {k:r[k]for k in ['path','bytes','sha256']}==pins[r['path']];matched+=1
pres=read(P/'preservation/preservation.json');assert pres['all_preserved']and pres['runtime_clean']and pres['runtime_head']=='844389ee069e1fb2e576708842d0b389b4d9a44a';assert(P/'context/shieldd.lock').read_bytes()==(G/'shieldd.lock').read_bytes()
mapping=read(P/'qualified/source-mapping.json')
for r in mapping['runtime_sources']:
 rel=re.sub('/+','/',r['path'].replace(chr(92),'/')).split('shieldd-pr160-844389ee/',1)[1];data=(W/'runtime-snapshot'/rel).read_bytes();assert len(data)==r['bytes']and sha(data)==r['sha256']
out=dict(kind='Independent original bytes/full types/standard axioms/import association/unchanged guard review; no compiler/native replay',manifest_entries=15,plan_pins=matched,fresh_modules=1,fresh_reports=5,full_declarations=reports,retained_reports=28,selected_custom_imports=2,external_modules=2141,guard_unchanged=True,native_execution='UNRUN',scope='Existential actual raw cache and exact Deferred/PerTx result derived from delivery success; index callback framing and concrete Rust refinement remain separate',full_transfer='OPEN')
(J/'endpoint-audit-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='full_declarations'}))
