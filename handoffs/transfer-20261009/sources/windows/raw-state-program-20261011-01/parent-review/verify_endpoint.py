"""Independent report/import/source/runtime/guard review, no compiler invocation."""
from pathlib import Path
import json,re,hashlib,ast
J=Path(__file__).parent;P=J/'packet01';W=J.parent.parent;G=W/'shared-build-handoff';Q=G/'handoffs/transfer-20261009/sources/windows/deferred-queue-20261011-01'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_bytes())
prior=J.parent/'windows-readback-publication-review01/verify_endpoint.py'
tree=ast.parse(prior.read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='parse');exec(compile(ast.Module(body=[fn],type_ignores=[]),str(prior),'exec'))
M=read(P/'manifest.json');R=read(P/'review.json');plan=read(P/'qualified/plan.json');pins={}
for e in M['entries']:
 b=(P/e['archive_path']).read_bytes();r=e['original'];assert len(b)==r['bytes']and sha(b)==r['sha256'];assert r['path']not in pins or pins[r['path']]==r;pins[r['path']]=r
assert len(M['entries'])==32
events=[json.loads(s)for s in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(events)==2
result=events[-1]['result'];assert result==R['compiler_result']and result['status']=='passed'
target=plan['targets'][0];assert len(plan['targets'])==1
source=P/'source/ShielddSecurity/TransferRawStateProgram01.lean';b=source.read_bytes();assert len(b)==target['source']['bytes']and sha(b)==target['source']['sha256'];assert {k:target['source'][k]for k in ['bytes','sha256']}=={k:target['predecessor_source'][k]for k in ['bytes','sha256']}
names=['ShielddSecurity.TransferRawStateProgram01.'+n for n in re.findall(r'^#check @([\w.]+)$',b.decode(),re.M)];assert names==target['audit_names'];assert len(names)==16
types=parse(P/'reports/fresh-16-complete-declarations.txt',names,result['audits'])
rp=P/'reports/fresh-16-complete-declarations.txt';assert len(rp.read_bytes())==result['stdout']['bytes']and sha(rp.read_bytes())==result['stdout']['sha256']
assert result['seconds']<240 and result['peak_rss_bytes']<4294967296 and result['command'][1:5]==['-j1','-M1536','-DmaxHeartbeats=300000','-DmaxRecDepth=4096'];assert result['command'][-1]==target['source']['path'] and result['command'][-2]==result['objects'][0]['path']
selected=read(P/'context/owned-composition-review.json');assert len(selected['selected'])==1
entry=selected['selected'][0];assert entry['module']=='TransferStateDelta' and plan['owned_imports']==[entry['copy']]
for k in ['bytes','sha256']:assert entry['copy'][k]==entry['object'][k]
assert (P/'source/ShielddSecurity/TransferStateDelta.lean').read_bytes()==(Q/'source/ShielddSecurity/TransferStateDelta.lean').read_bytes()
assert target['imports']==['ShielddSecurity.TransferStateDelta']
oldnames=['ShielddSecurity.TransferStateDelta.'+n for n in re.findall(r'^#check @([\w.]+)$',(P/'source/ShielddSecurity/TransferStateDelta.lean').read_text(),re.M)]
retained=parse(P/'reports/inherited-12-complete-declarations.txt',oldnames,R['inherited_audits']);assert len(retained)==12 and R['inherited_audits']==selected['inherited_public_reports']
prior_retained=read(Q/'proof-audits/inherited-12.json');assert retained==prior_retained['audits']
ref=read(P/'context/core-floor-reference.json');floor=Q/'context/core-external-floor.json';assert len(floor.read_bytes())==ref['original']['bytes']and sha(floor.read_bytes())==ref['original']['sha256'];assert plan['external_floor']==ref['original']
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
for f in(P/'runtime').rglob('*.rs'):assert f.read_bytes()==(W/'runtime-snapshot'/f.relative_to(P/'runtime')).read_bytes()
assert(P/'context/shieldd.lock').read_bytes()==(G/'shieldd.lock').read_bytes()
pres=read(P/'preservation/preservation.json');assert pres['all_preserved']and pres['runtime_clean']and pres['runtime_head']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
bad=[json.loads(s)for s in(P/'rejected/events.jsonl').read_text().splitlines()];assert len(bad)==2 and bad[-1]['result']['status']=='failed'
repaired=(P/'rejected/source.lean').read_text()
for old,new in [('prefix','earlierCommands'),('partial','failureCache'),('unit','returnedUnit')]:repaired=re.sub(r'\b'+old+r'\b',new,repaired)
repaired=repaired.replace('delivery_failure_preserves_parent_and_queue _ _ _ _ _ _ _ _\n','delivery_failure_preserves_parent_and_queue _ _ _ _ _ _ _\n',1);assert repaired==source.read_text()
out=dict(kind='Independent original bytes/full reports/import closure/unchanged guard review; no compiler/native replay',files_rehashed=32,plan_pins=matched,fresh_modules=1,fresh_reports=16,retained_reports=12,full_declarations=types,inherited_declarations=retained,custom_import=entry,external_modules=2141,guards_unchanged=True,rejected_predecessors=1,rejected_proof_result=0,native_execution='UNRUN',full_transfer='OPEN')
(J/'endpoint-audit-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['full_declarations','inherited_declarations','custom_import']}))
