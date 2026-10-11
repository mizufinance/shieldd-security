"""Independent original-byte, declaration, import-context and guard review; no compiler."""
from pathlib import Path
import json,re,hashlib
J=Path(__file__).parent;P=J/'packet01';G=J.parent.parent/'shared-build-handoff';W=J.parent.parent
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_bytes())
M=read(P/'manifest.json');R=read(P/'review.json');plan=read(P/'qualified/plan.json')
pins={}
for e in M['entries']:
 b=(P/e['archive_path']).read_bytes();r=e['original']
 assert len(b)==r['bytes'] and sha(b)==r['sha256']
 assert r['path'] not in pins or pins[r['path']]==r
 pins[r['path']]=r
assert len(M['entries'])==32
def parse(path,names,expected):
 b=path.read_bytes();s=b.decode();assert not re.search(r'\b(?:error|warning|info|trace):|sorryAx',s)
 lines=s.splitlines();result={};pos=0;types=[]
 for name in names:
  assert lines[pos].startswith((name+' :','@'+name+' :'))
  start=pos;pos+=1
  while pos<len(lines) and lines[pos].startswith((' ','\t')):pos+=1
  signature='\n'.join(lines[start:pos])
  ax=lines[pos];pos+=1
  while ax.endswith(',') and pos<len(lines):
   ax+='\n'+lines[pos];pos+=1
  assert ax.startswith("'"+name+"' ")
  if ax=="'"+name+"' does not depend on any axioms":a=[]
  else:
   match=re.fullmatch("'"+re.escape(name)+"' depends on axioms: \\[([^\\]]*)\\]",ax);assert match,(name,ax)
   a=[v.strip() for v in match[1].split(',') if v.strip()]
  assert set(a)<={'propext','Classical.choice','Quot.sound'}
  result[name]={'axioms':a,'full_type_sha256':sha(signature.encode())}
  types.append({'declaration':name,'full_type':signature,**result[name]})
 assert pos==len(lines) and result==expected
 return types
fresh=P/'source/ShielddSecurity/TransferDeferredQueueSourceModel01.lean'
source=fresh.read_text();names=re.findall(r'^#check @([\w.]+)$',source,re.M)
assert names==plan['targets'][0]['audit_names'] and len(names)==17
assert re.findall(r'^#print axioms ([\w.]+)$',source,re.M)==names
decls=re.findall(r'^(?:inductive|structure|abbrev|def|theorem) ([\w]+)',source,re.M)
assert ['ShielddSecurity.TransferDeferredQueueSourceModel01.'+v for v in decls]==names
f=parse(P/'reports/fresh-17-complete-declarations.txt',names,R['fresh_audits'])
old=P/'source/ShielddSecurity/TransferStateDelta.lean';om=read(P/'inherited/manifest.json')
on=['ShielddSecurity.TransferStateDelta.'+n for n in om['theorems']]
assert len(on)==12 and sha(old.read_bytes())==om['sha256']
assert re.findall(r'^#check @([\w.]+)$',old.read_text(),re.M)==om['theorems']
i=parse(P/'reports/inherited-12-complete-declarations.txt',on,R['inherited_audits'])
for name in ['exit.txt','lean-exit.txt']:assert (P/'inherited'/name).read_text().strip()=='0'
record=R['compiler_result'];events=[json.loads(l) for l in (P/'qualified/events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[1]['result']==record and record['status']=='passed'
assert record['audits']==R['fresh_audits'] and record['peak_rss_bytes']<4294967296 and record['seconds']<240
assert record['command'][1:5]==['-j1','-M1536','-DmaxHeartbeats=300000','-DmaxRecDepth=4096']
assert record['stdout']==R['compiler_output'] and record['stdout']['sha256']==sha((P/'reports/fresh-17-complete-declarations.txt').read_bytes())
matched=0
for r in plan['pins']:
 if r['path'] in pins:assert {k:r[k] for k in ['path','bytes','sha256']}==pins[r['path']];matched+=1
comp=read(P/'context/owned-composition-review.json');selected=comp['selected'];assert len(selected)==1
entry=selected[0];assert entry['module']=='TransferStateDelta'
assert entry['source']['sha256']==om['sha256'] and entry['source']['bytes']==len(old.read_bytes())
assert {k:entry['object'][k] for k in ['bytes','sha256']}=={k:entry['copy'][k] for k in ['bytes','sha256']}
assert plan['owned_imports']==[entry['copy']] and comp['inherited_public_reports']==R['inherited_audits']
assert entry['copy']['path'].startswith(plan['lean_path'][0]+'\\')
assert plan['targets'][0]['imports']==['ShielddSecurity.TransferStateDelta']
floor=read(P/'context/core-external-floor.json');seen=set();todo=['Lean','Init']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);e=floor['modules'][n];todo.extend(e['imports'])
 if e['implicit_Init']:todo.append('Init')
assert seen==set(floor['modules']) and len(seen)==2141 and floor['gaps']==[]
external={}
for e in floor['modules'].values():
 for r in [e['source'],*e['objects']]:
  assert r['path'] not in external or external[r['path']]==r
  external[r['path']]=r
assert external=={r['path']:r for r in floor['immutable_files']}
assert plan['external_floor']['sha256']==sha((P/'context/core-external-floor.json').read_bytes())
runner=P/'qualified/execute_bounded.py';prior=G/'handoffs/transfer-20261009/sources/windows/capability-envelope-20261011-01/execution-context/transfer-proof-admission-20261010-02/execute_bounded.py'
assert runner.read_bytes()==prior.read_bytes()
assert plan['limits']['threads']==1 and plan['limits']['heap_mib']==1536
assert plan['pressure_limits']=={'commit_preflight_mib':1792,'commit_running_mib':512,'free_disk_bytes':2147483648,'one_host_one_heavy':True,'owned_job_memory_and_rss_bytes':4294967296,'physical_preflight_mib':2560,'physical_running_mib':1536}
runtime=W/'runtime-snapshot'
for file in (P/'runtime').rglob('*.rs'):
 assert file.read_bytes()==(runtime/file.relative_to(P/'runtime')).read_bytes()
assert (P/'context/shieldd.lock').read_bytes()==(G/'shieldd.lock').read_bytes()
failed=[]
for n in ['01','02']:
 rp=P/'rejected'/n;event=[json.loads(l) for l in (rp/'events.jsonl').read_text().splitlines()][-1]
 assert event['result']['status']=='failed'
 failed.append({'attempt':n,'status':'failed','result':event['result'],'source_sha256':sha((rp/'source.lean').read_bytes())})
out={'kind':'Parent independent full original bytes/types/axioms, first-package context and unchanged guard review; no Lean or native replay','files_rehashed':32,'plan_pin_records_matched':matched,'fresh_declarations':f,'inherited_declarations':i,'first_package_custom_associations':1,'external_core_modules':2141,'external_pin_records':len(external),'external_physical_rehash':'Producer original retained closure; runner checks all reachable pins before/after. Parent verifies record closure, not Windows artifacts.','unchanged_runner':True,'runtime_source_files_exact':2,'rejected_attempts':failed,'native_execution':'UNRUN','Rust_refinement':'OPEN','durable_recovery':'OPEN','full_transfer':'OPEN'}
(J/'endpoint-audit-review01.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['files_rehashed','plan_pin_records_matched','first_package_custom_associations','external_core_modules','external_pin_records','unchanged_runner','runtime_source_files_exact']}))
