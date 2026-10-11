"""Independent batch program source, original reports/imports and physical guard review."""
from pathlib import Path
import json,re,hashlib,ast,difflib
J=Path(__file__).parent;P=J/'packet01';W=J.parent.parent;G=W/'shared-build-handoff';Q=G/'handoffs/transfer-20261009/sources/windows/deferred-queue-20261011-01';A=G/'handoffs/transfer-20261009/sources/windows/raw-state-program-20261011-01';V=G/'handoffs/transfer-20261009/sources/windows/reader-vector-20261011-01'
def read(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
prior=J.parent/'windows-readback-publication-review01/verify_endpoint.py';tree=ast.parse(prior.read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='parse');exec(compile(ast.Module(body=[fn],type_ignores=[]),str(prior),'exec'))
M=read(P/'manifest.json');R=read(P/'review.json');plan=read(P/'qualified/plan.json');pins={}
for e in M['entries']:
 b=(P/e['archive_path']).read_bytes();r=e['original'];assert len(b)==r['bytes']and sha(b)==r['sha256'];pins[r['path']]=r
assert len(plan['targets'])==1
t=plan['targets'][0];b=(P/'source/ShielddSecurity/TransferNullifierBatchSource01.lean').read_bytes();assert len(b)==t['source']['bytes']and sha(b)==t['source']['sha256'];assert all(t['source'][k]==t['predecessor_source'][k]for k in ['bytes','sha256'])
text=b.decode();names=['ShielddSecurity.TransferNullifierBatchSource01.'+n for n in re.findall(r'^#check @([\w.]+)\s*$',text,re.M)];assert names==t['audit_names']and len(names)==16
public=re.findall(r'^(?:def|theorem|structure|inductive) ([\w.]+)',text,re.M);assert names==['ShielddSecurity.TransferNullifierBatchSource01.'+n for n in public]
assert re.findall(r'^import ([\w.]+)',text,re.M)==t['imports']==['ShielddSecurity.TransferRawStateProgram01','ShielddSecurity.TransferNullifierReaderVector01'];assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',text)
events=[json.loads(l)for l in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(events)==2;result=events[-1]['result'];assert result==R['compiler_result']and result['status']=='passed'
reports=parse(P/'reports/fresh-16-complete-declarations.txt',names,result['audits']);raw=(P/'reports/fresh-16-complete-declarations.txt').read_bytes();assert len(raw)==result['stdout']['bytes']and sha(raw)==result['stdout']['sha256']
assert result['seconds']<240 and result['peak_rss_bytes']<4294967296 and result['command'][1:5]==['-j1','-M1536','-DmaxHeartbeats=300000','-DmaxRecDepth=4096'];assert result['command'][-1]==t['source']['path']and result['command'][-2]==result['objects'][0]['path']
ref=read(P/'context/inherited-reference.json');core=ref['core_floor'];floor=Q/'context/core-external-floor.json';r=core['original'];assert len(floor.read_bytes())==r['bytes']and sha(floor.read_bytes())==r['sha256'];assert plan['external_floor']==r;assert core['accepted_evidence_commit']=='7f4abf584595911545bd8a7645e487c629931cba'
F=read(floor);seen=set();todo=['Lean','Init']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);e=F['modules'][n];todo.extend(e['imports'])
 if e['implicit_Init']:todo.append('Init')
assert len(seen)==2141 and seen==set(F['modules'])and F['gaps']==[]
inherited=read(A/'parent-review/endpoint-audit-review01.json');vec=read(V/'parent-review/endpoint-audit-review01.json');audits={e['declaration']:{k:e[k]for k in ['axioms','full_type_sha256']}for e in inherited['full_declarations']+inherited['inherited_declarations']+vec['full_declarations']};assert len(audits)==41
owned=read(P/'context/owned-composition-review.json');assert owned['inherited_public_reports']==audits and len(owned['selected'])==3
objects={'TransferStateDelta':inherited['custom_import']['object'],'TransferRawStateProgram01':read(A/'review.json')['compiler_result']['objects'][0],'TransferNullifierReaderVector01':read(V/'review.json')['compiler_result']['objects'][0]}
for key,doc,commit in [('raw',A,'ae307b2af3c98242cc6a3be82e5673d89b54f9c4'),('vector',V,'2aae019bc518264d59e4d0ba590ada1d478c91f5')]:
 m=(doc/'manifest.json').read_bytes();assert len(m)==ref[key]['manifest']['bytes']and sha(m)==ref[key]['manifest']['sha256'];assert ref[key]['accepted_evidence_commit']==commit
for e in owned['selected']:
 n=e['module'];doc=V if n=='TransferNullifierReaderVector01'else A;source=(doc/'source/ShielddSecurity'/(n+'.lean')).read_bytes();assert len(source)==e['source']['bytes']and sha(source)==e['source']['sha256'];assert all(e['object'][k]==objects[n][k]==e['copy'][k]for k in ['bytes','sha256'])
assert plan['owned_imports']==[e['copy']for e in owned['selected']]
assert(P/'qualified/execute_bounded.py').read_bytes()==(Q/'qualified/execute_bounded.py').read_bytes();assert plan['pressure_limits']=={'commit_preflight_mib':1792,'commit_running_mib':512,'free_disk_bytes':2147483648,'one_host_one_heavy':True,'owned_job_memory_and_rss_bytes':4294967296,'physical_preflight_mib':2560,'physical_running_mib':1536}
for file in(P/'runtime').rglob('*.rs'):assert file.read_bytes()==(W/'runtime-snapshot'/file.relative_to(P/'runtime')).read_bytes()
assert(P/'context/shieldd.lock').read_bytes()==(G/'shieldd.lock').read_bytes();pres=read(P/'preservation/preservation.json');assert pres['all_preserved']and pres['runtime_clean']and pres['runtime_head']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
old=(P/'rejected/source.lean').read_text();new=text.replace('\r\n','\n');contracts=lambda s:[m.group(0).split(' :=')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^set_option pp.all|\Z)',s)];assert contracts(old)==contracts(new)
definitions=lambda s:[m.group(0).strip()for m in re.finditer(r'(?m)^(?:def|structure|inductive) [\s\S]*?(?=^(?:def|structure|inductive|theorem|set_option pp.all)|\Z)',s)];assert definitions(old)==definitions(new)
re=[json.loads(l)for l in(P/'rejected/events.jsonl').read_text().splitlines()];assert len(re)==2 and re[-1]['result']['status']=='failed'and re[-1]['result']['reason']=='Lean exit 1'
matched=0
for r in plan['pins']:
 if r['path']in pins:assert {k:r[k]for k in ['path','bytes','sha256']}==pins[r['path']];matched+=1
out=dict(kind='Independent source/full-type/standard-axiom/inherited associations/runtime/guard review; no compiler/native replay',manifest_entries=len(M['entries']),plan_pins_matched=matched,fresh_modules=1,fresh_reports=16,full_declarations=reports,inherited_reports=41,custom_imports=owned['selected'],core_modules=2141,guard_unchanged=True,rejected=dict(result=re[-1]['result'],compiler_output=(P/'rejected/compiler-output.txt').read_text(),proof_step_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True))),program_definitions_and_theorem_contracts_unchanged=True),interfaces=R['interfaces'],scope='Successful modeled source-order checks derive ordered append, capacity under explicit capacity<wordMax, observed per-input freshness and one object write; errors retain supplied input cache with any earlier effects',native_execution='UNRUN',full_transfer='OPEN')
(J/'endpoint-audit-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['full_declarations','rejected','custom_imports','interfaces']}))
