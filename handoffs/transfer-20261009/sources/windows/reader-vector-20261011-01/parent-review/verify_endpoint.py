"""Independent original vector proof, imports, runtime identity and guard review."""
from pathlib import Path
import json,re,hashlib,ast,difflib
J=Path(__file__).parent;P=J/'packet01';W=J.parent.parent;G=W/'shared-build-handoff';Q=G/'handoffs/transfer-20261009/sources/windows/deferred-queue-20261011-01';A=G/'handoffs/transfer-20261009/sources/windows/readback-publication-20261011-01'
def read(p):return json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
prior=J.parent/'windows-readback-publication-review01/verify_endpoint.py';tree=ast.parse(prior.read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='parse');exec(compile(ast.Module(body=[fn],type_ignores=[]),str(prior),'exec'))
M=read(P/'manifest.json');R=read(P/'review.json');plan=read(P/'qualified/plan.json');pins={}
for e in M['entries']:
 b=(P/e['archive_path']).read_bytes();r=e['original'];assert len(b)==r['bytes']and sha(b)==r['sha256'];pins[r['path']]=r
assert len(plan['targets'])==1
t=plan['targets'][0];b=(P/'source/ShielddSecurity/TransferNullifierReaderVector01.lean').read_bytes();assert len(b)==t['source']['bytes']and sha(b)==t['source']['sha256'];assert all(t['source'][k]==t['predecessor_source'][k]for k in ['bytes','sha256'])
text=b.decode();names=['ShielddSecurity.TransferNullifierReaderVector01.'+n for n in re.findall(r'^#check @([\w.]+)\s*$',text,re.M)];assert names==t['audit_names']and len(names)==13
public=re.findall(r'^(?:def|theorem) ([\w.]+)',text,re.M);assert names==['ShielddSecurity.TransferNullifierReaderVector01.'+n for n in public]
assert re.findall(r'^import ([\w.]+)',text,re.M)==t['imports']==['Lean'];assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',text)
events=[json.loads(l)for l in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(events)==2;result=events[-1]['result'];assert result==R['compiler_result']and result['status']=='passed'
reports=parse(P/'reports/fresh-13-complete-declarations.txt',names,result['audits']);raw=(P/'reports/fresh-13-complete-declarations.txt').read_bytes();assert len(raw)==result['stdout']['bytes']and sha(raw)==result['stdout']['sha256']
assert result['seconds']<240 and result['peak_rss_bytes']<4294967296 and result['command'][1:5]==['-j1','-M1536','-DmaxHeartbeats=300000','-DmaxRecDepth=4096'];assert result['command'][-1]==t['source']['path']and result['command'][-2]==result['objects'][0]['path']
ref=read(P/'context/context-reference.json');core=ref['core_floor'];floor=Q/'context/core-external-floor.json';r=core['original'];assert len(floor.read_bytes())==r['bytes']and sha(floor.read_bytes())==r['sha256'];assert plan['external_floor']==r;assert core['accepted_evidence_commit']=='7f4abf584595911545bd8a7645e487c629931cba'
F=read(floor);seen=set();todo=['Lean','Init']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);e=F['modules'][n];todo.extend(e['imports'])
 if e['implicit_Init']:todo.append('Init')
assert len(seen)==2141 and seen==set(F['modules'])and F['gaps']==[]
assert plan['owned_imports']==[]and read(P/'context/empty-owned-composition-review.json')['selected']==[]
assert(P/'qualified/execute_bounded.py').read_bytes()==(Q/'qualified/execute_bounded.py').read_bytes()
assert plan['pressure_limits']=={'commit_preflight_mib':1792,'commit_running_mib':512,'free_disk_bytes':2147483648,'one_host_one_heavy':True,'owned_job_memory_and_rss_bytes':4294967296,'physical_preflight_mib':2560,'physical_running_mib':1536}
up=ref['upstream_status_authentication'];am=(A/'manifest.json').read_bytes();assert len(am)==up['accepted_manifest']['bytes']and sha(am)==up['accepted_manifest']['sha256'];assert up['accepted_evidence_commit']=='35998917369a3d6479771403bba3f206a1a8ebb3'
types=read(A/'parent-review/endpoint-audit-review01.json')['full_declarations'];retained={e['declaration']:{k:e[k]for k in ['axioms','full_type_sha256']}for e in types if e['declaration'].startswith('ShielddSecurity.TransferReadback.')};assert len(retained)==17 and retained==up['complete_reports']
src=(A/'source/ShielddSecurity/TransferReadback.lean').read_bytes();assert len(src)==up['source']['bytes']and sha(src)==up['source']['sha256']
for file in(P/'runtime').rglob('*.rs'):assert file.read_bytes()==(W/'runtime-snapshot'/file.relative_to(P/'runtime')).read_bytes()
assert(P/'context/shieldd.lock').read_bytes()==(G/'shieldd.lock').read_bytes();pres=read(P/'preservation/preservation.json');assert pres['all_preserved']and pres['runtime_clean']and pres['runtime_head']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
rejected=[]
for n in [1,2]:
 d=P/('rejected-'+str(n));e=[json.loads(l)for l in(d/'events.jsonl').read_text().splitlines()];assert len(e)==2 and e[-1]['result']['status']=='failed'and e[-1]['result']['reason']=='Lean exit 1';s=(d/'source.lean').read_text();assert re.findall(r'^(?:def|theorem) ([\w.]+)',s,re.M)==public
 # All maintained recurrence definitions and theorem contracts are unchanged.
 contracts=lambda s: [m.group(0).split(' :=')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^set_option pp.all|\Z)',s.replace('\r\n','\n'))]
 assert contracts(s)==contracts(text)
 rejected.append(dict(attempt=n,result=e[-1]['result'],source_sha256=sha((d/'source.lean').read_bytes()),compiler_output=(d/'compiler-output.txt').read_text(),scope='Rejected elaboration; no semantic negative result'))
matched=0
for r in plan['pins']:
 if r['path']in pins:assert {k:r[k]for k in ['path','bytes','sha256']}==pins[r['path']];matched+=1
out=dict(kind='Independent original source/full-type/axiom/core closure/guard/runtime review; no compiler or native replay',manifest_entries=len(M['entries']),plan_pins_matched=matched,fresh_modules=1,fresh_reports=13,full_declarations=reports,separate_status_context_reports=17,custom_imports=0,core_modules=2141,guard_unchanged=True,rejected_attempts=rejected,interfaces=R['interfaces'],scope='Success derives exact vector alignment/length and exhaustive observed durable/pending freshness; status authentication and actual Rust Vec/store/Merkle refinement remain upstream',native_execution='UNRUN',full_transfer='OPEN')
(J/'endpoint-audit-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['full_declarations','rejected_attempts','interfaces']}))
