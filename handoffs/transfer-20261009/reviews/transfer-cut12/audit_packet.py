"""Freeze sealed Cut12 and independently inspect existing evidence; never invoke Lean."""
import sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
import hashlib,json,re,runpy,shutil
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[1];S=R/'work/mac-transfer-cut12';O=R/'outputs/mac-transfer-cut12';REPO=R/'work/shared-build-handoff';F=H/'frozen'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
producer=O/'publication-manifest01.json';envelope=O/'seal-envelope01.json'
assert sha(producer)=='cf1511163550fb7e788df052bdef1837dd464f5cc7a0d6b17ab19f07f27f5a45'
m=json.loads(producer.read_bytes());e=json.loads(envelope.read_bytes());assert e['producer_manifest_sha256']==sha(producer)
entries=dict(m['files']);assert not set(entries)&set(e['entries']);entries.update(e['entries'])
if not F.exists():F.mkdir()
for n,x in entries.items():
 p=R/n;assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes'];out=F/n;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,out)
for p in [producer,envelope]:shutil.copyfile(p,F/p.name)
(H/'freeze-manifest01.json').write_text(json.dumps(dict(files=entries,producer_sha256=sha(producer),envelope_sha256=sha(envelope)),indent=2)+'\n')
auditor=F/'work/mac-transfer-cut12/audit_log.py';validate=runpy.run_path(str(auditor))['validate'];accepted=[];failed=[]
for name in sorted(p.stem for p in (S/'project/ShielddSecurity').glob('TransferCut12*.lean')):
 receipts=sorted(O.glob('build-'+name+'-*.json'));passed=[]
 for p in receipts:
  d=json.loads(p.read_bytes())
  if d['status']=='passed':passed.append((p,d))
  else:failed.append(dict(path=str(p.relative_to(R)),sha256=sha(p),status=d['status'],credit=0))
 assert len(passed)==1
 p,d=passed[0];src=S/'project/ShielddSecurity'/(name+'.lean');obj=S/'project/.lake/build/lib/lean/ShielddSecurity'/(name+'.olean');log=F/str(p.with_suffix('.log').relative_to(R))
 assert d['exit']==0 and sha(src)==d['source_sha256'] and sha(obj)==d['object_sha256'] and sha(log)==d['log_sha256']
 parsed=validate(log.read_text(),d['expected_axiom_names'],d['expected_signature_names']);assert parsed['axiom_audits']==d['axiom_audits'] and parsed['full_signature_sha256']==d['full_signature_sha256']
 assert d['timeout_seconds']==240 and d['lean_heap_limit_MiB']==2048 and d['process_group_rss_limit_bytes']==4294967296 and d['seconds']<=240 and d['peak_group_rss_bytes']<=4294967296 and d['minimum_memory_free_percent']>=15 and d['minimum_disk_free_bytes']>=2147483648
 for module,x in d['frozen_imports'].items():
  if not module.startswith('ShielddSecurity.'):continue
  leaf=module.split('.')[-1];assert sha(S/'project/ShielddSecurity'/(leaf+'.lean'))==x['source_sha256'] and sha(S/'project/.lake/build/lib/lean/ShielddSecurity'/(leaf+'.olean'))==x['object_sha256']
 accepted.append(dict(module=name,receipt_sha256=sha(p),source_sha256=sha(src),object_sha256=sha(obj),audits=parsed,seconds=d['seconds'],peak_group_rss_bytes=d['peak_group_rss_bytes']))
assert len(accepted)==7 and sum(x['audits']['axiom_audits'] for x in accepted)==61 and len(failed)==3
inh=json.loads((O/'inherited-qualification01.json').read_bytes());assert inh['kernel_runs']==0
closure=set()
def visit(name):
 if name in closure:return
 closure.add(name);p=S/'project/ShielddSecurity'/(name+'.lean');assert p.exists()
 for dep in re.findall(r'(?m)^import ShielddSecurity\.([\w]+)',p.read_text()):visit(dep)
visit('TransferCut12Joined01');new=set(x['module'] for x in accepted);root_new=closure&new;inherited=closure-new
assert root_new=={'TransferCut12Joined01','TransferCut12Proof01','TransferCut12Data01'}
context=H/'accepted-context';context.mkdir(exist_ok=True);bindings={}
for name in sorted(inherited):
 x=inh['reused'][name];src=S/'project/ShielddSecurity'/(name+'.lean');obj=S/'project/.lake/build/lib/lean/ShielddSecurity'/(name+'.olean');canonical=REPO/'circuits/ShielddSecurity'/(name+'.lean')
 assert sha(src)==x['source_sha256'] and sha(obj)==x['object_sha256'] and sha(R/x['original_receipt_path'])==x['original_receipt_sha256']
 assert canonical.exists() and sha(canonical)==sha(src),name
 shutil.copyfile(src,context/src.name);bindings[name]=x
(H/'accepted-context-manifest01.json').write_text(json.dumps(bindings,indent=2)+'\n')
assert len(root_new)==3 and sum(x['audits']['axiom_audits'] for x in accepted if x['module'] in root_new)==39
types=json.loads((O/'full-audits01.json').read_bytes());assert len(types)==61
metadata_refusals=[]
for t in types:
 if hashlib.sha256(t['full_type'].encode()).hexdigest()!=t['full_type_sha256']:
  match=re.search(r'^@?'+re.escape(t['name'])+r'\s*:[\s\S]*$',t['full_type'],re.M);assert match and hashlib.sha256(match.group(0).strip().encode()).hexdigest()==t['full_type_sha256'];metadata_refusals.append(dict(name=t['name'],reason='Preceding linter warning included in producer full_type field',credit=0))
 assert t['name'] in next(x for x in accepted if t['name'].startswith('ShielddSecurity.'+x['module']+'.'))['audits']['full_signature_sha256']
assert len(metadata_refusals)==2
result=dict(status='kernel_output_audit_passed_structured_metadata_successor_pending',structured_metadata_refusals=metadata_refusals,producer_manifest_sha256=sha(producer),envelope_sha256=sha(envelope),entries_rehashed=len(entries),fresh_modules=accepted,all_stage_modules=7,all_stage_audits=61,root_owned_modules=len(closure),root_new_modules=3,root_new_audits=39,root_inherited_modules=len(inherited),inherited_exact_source_object_receipt_canonical_checks=len(bindings),failed_attempts=failed,parent_kernel_runs=0,scope=json.loads((O/'scope01.json').read_bytes()),full_transfer='OPEN')
(H/'packet-review01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k in ['status','entries_rehashed','all_stage_modules','all_stage_audits','root_owned_modules','root_new_modules','root_new_audits','root_inherited_modules','parent_kernel_runs']}))
