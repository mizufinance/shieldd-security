"""Independent original report/source/import/guard review; no compiler or native run."""
from pathlib import Path
import json,re,hashlib
J=Path(__file__).parent;P=J/'packet01';W=J.parent.parent;G=W/'shared-build-handoff'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_bytes())
M=read(P/'manifest.json');R=read(P/'review.json');plan=read(P/'qualified/plan.json');pins={}
for e in M['entries']:
 b=(P/e['archive_path']).read_bytes();r=e['original'];assert len(b)==r['bytes']and sha(b)==r['sha256'];assert r['path']not in pins or pins[r['path']]==r;pins[r['path']]=r
assert len(M['entries'])==22
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
events=[json.loads(l)for l in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(events)==6
results=[e['result']for e in events if 'result'in e];assert results==R['compiler_results']and len(results)==3
alltypes=[];modules=[]
for index,(target,result)in enumerate(zip(plan['targets'],results)):
 n=target['module'];source=P/'source/ShielddSecurity'/(n+'.lean');b=source.read_bytes();assert len(b)==target['source']['bytes']and sha(b)==target['source']['sha256'];assert {k:target['source'][k]for k in ['bytes','sha256']}=={k:target['predecessor_source'][k]for k in ['bytes','sha256']}
 local=re.findall(r'^#check @([\w.]+)$',b.decode(),re.M);names=['ShielddSecurity.'+n+'.'+v for v in local];assert names==target['audit_names'];assert local==re.findall(r'^#print axioms ([\w.]+)$',b.decode(),re.M)
 assert re.findall(r'^theorem ([\w]+)',b.decode(),re.M)==local
 imports=re.findall(r'^import ([\w.]+)',b.decode(),re.M);assert imports==target['imports'];assert all(not dep.startswith('ShielddSecurity.')or dep.split('.')[-1]in [v['module']for v in plan['targets'][:index]]for dep in imports)
 rp=P/'reports'/(n+'-complete-types-and-axioms.txt');alltypes+=parse(rp,names,result['audits']);assert len(rp.read_bytes())==result['stdout']['bytes']and sha(rp.read_bytes())==result['stdout']['sha256']
 assert result['status']=='passed'and result['seconds']<240 and result['peak_rss_bytes']<4294967296
 assert result['command'][1:5]==['-j1','-M1536','-DmaxHeartbeats=300000','-DmaxRecDepth=4096'];assert result['command'][-1]==target['source']['path'];assert len(result['objects'])==1 and result['command'][-2]==result['objects'][0]['path']
 modules.append(dict(module=n,source=target['source'],report=result['stdout'],audits=len(names),objects=result['objects'],seconds=result['seconds'],peak_rss_bytes=result['peak_rss_bytes']))
assert len(alltypes)==35 and R['audits']==[v['declaration']for v in alltypes]
ref=read(P/'context/core-floor-reference.json');accepted=G/'handoffs/transfer-20261009/sources/windows/deferred-queue-20261011-01/context/core-external-floor.json';floor=read(accepted)
assert len(accepted.read_bytes())==ref['original']['bytes']and sha(accepted.read_bytes())==ref['original']['sha256'];assert plan['external_floor']==ref['original'];assert ref['accepted_evidence_commit']=='7f4abf584595911545bd8a7645e487c629931cba'
seen=set();todo=['Lean','Init']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);e=floor['modules'][n];todo.extend(e['imports'])
 if e['implicit_Init']:todo.append('Init')
assert len(seen)==2141 and seen==set(floor['modules'])and floor['gaps']==[]
assert all(not v.startswith('ShielddSecurity.')and v in seen for v in plan['targets'][0]['imports'])
assert plan['owned_imports']==[]and read(P/'context/empty-owned-composition-review.json')['selected']==[]
runner=P/'qualified/execute_bounded.py';prior=G/'handoffs/transfer-20261009/sources/windows/deferred-queue-20261011-01/qualified/execute_bounded.py';assert runner.read_bytes()==prior.read_bytes()
assert plan['limits']['threads']==1 and plan['limits']['heap_mib']==1536 and plan['limits']['max_heartbeats']==300000 and plan['limits']['max_rec_depth']==4096
assert plan['pressure_limits']=={'commit_preflight_mib':1792,'commit_running_mib':512,'free_disk_bytes':2147483648,'one_host_one_heavy':True,'owned_job_memory_and_rss_bytes':4294967296,'physical_preflight_mib':2560,'physical_running_mib':1536}
matched=0
for r in plan['pins']:
 if r['path']in pins:assert {k:r[k]for k in ['path','bytes','sha256']}==pins[r['path']];matched+=1
for file in(P/'runtime').rglob('*.rs'):assert file.read_bytes()==(W/'runtime-snapshot'/file.relative_to(P/'runtime')).read_bytes()
assert (P/'context/shieldd.lock').read_bytes()==(G/'shieldd.lock').read_bytes();preservation=read(P/'preservation/preservation.json');assert preservation['all_preserved']and preservation['runtime_clean']and preservation['runtime_head']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
out=dict(kind='Independent original byte/type/axiom/selected import and unchanged guard review; no compiler/native replay',files_rehashed=22,plan_pin_records_matched=matched,modules=modules,complete_reports=35,full_declarations=alltypes,custom_imports='All three exact sources freshly compiled in dependency order; empty retained owned floor',external_core_modules=2141,external_closure_identity=ref['original'],external_physical_rehash='Original guarded producer before/after; parent verifies accepted metadata and record closure only',guard_unchanged=True,runtime_source_files=3,source_scope='Symbolic readback/recovery/publication programs, not complete concrete Host phase model or Rust/NOMT/codec/durability refinement',native_execution='UNRUN',full_transfer='OPEN')
(J/'endpoint-audit-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(files=22,reports=35,modules=3,plan_pins=matched,core_modules=2141)))
