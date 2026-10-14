"""Atomically reconcile compact Windows replacements with accepted contracts."""
from pathlib import Path
import argparse,hashlib,json,os,re,tarfile
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--repository',type=Path,required=True);ap.add_argument('--reports-root',type=Path,required=True);ap.add_argument('--official-archive',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
repo=a.repository.resolve();out=a.output.resolve();assert not out.exists()
def ident(b):return dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def short(r):return {k:r[k]for k in ['bytes','sha256']}
def checked(p,r):
 b=p.read_bytes();assert ident(b)==short(r),str(p);return b
def load(p):return json.loads(p.read_bytes())
review=load(root/'baseline-review.json');prior=json.loads(checked(repo/review['prior_packing']['path'],review['prior_packing']))
assert prior['status']=='passed' and prior['runtime_sha']==review['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
owned=dict(prior['modules']);assert len(owned)==8
with tarfile.open(a.official_archive)as ar:
 b=ar.extractfile('original/transfer-external-floor-complete-20261010-08/external-floor.json').read();assert ident(b)==review['external_parent'];oldfloor=json.loads(b)
oldpins={(r['path'],r['bytes'],r['sha256'])for r in oldfloor['immutable_files']}
modules={};reports=[];packets=[];seconds=0;sources={}
for record in review['packets']:
 name=record['module'];packet=a.reports_root/record['packet'];saved=root/'packets'/record['packet']
 raw=checked(saved/'manifest.json',record['manifest']);assert raw==checked(packet/'manifest.json',record['manifest']);manifest=json.loads(raw)
 assert manifest['exact_runtime_sha']==review['runtime_sha'] and manifest['owned_modules']==[name]
 assert not manifest['certification'] and manifest['native_credit']==manifest['new_cumulative_credit']==0 and not manifest['legacy_owned_objects_reused']
 prefix=Path('variants')/record['packet']
 for item in manifest['members']:checked(packet/Path(item['member']).relative_to(prefix),item)
 meta=packet/'original-metadata'
 for item in manifest['archive_members']:checked(meta/item['member'],item)
 plan=load(meta/'plan.json');external=load(meta/'external-floor.json');floor=load(meta/'owned-floor/composition-review.json')
 assert ident((meta/'external-floor.json').read_bytes())==short(plan['external_floor'])
 assert ident((meta/'owned-floor/composition-review.json').read_bytes())==short(plan['owned_import_pool'])
 assert external['parent_floor_identity']['sha256']==review['external_parent']['sha256'] and external['admission_ready'] and not external['gaps']
 for n,r in external['modules'].items():assert oldfloor['modules'][n]==r,n
 assert all((r['path'],r['bytes'],r['sha256'])in oldpins for r in external['immutable_files'])
 assert floor['admission_ready'] and floor['kernel_credit']==0
 assert {x['module']for x in floor['selected']}==set(owned)
 assert plan['owned_imports']==[x['copy']for x in floor['selected']]
 for item in floor['selected']:
  old=owned[item['module']];assert short(item['source'])==old['source'],item['module']
  assert item['object']in old['objects'] and short(item['copy'])==short(item['object']),item['module']
  old['objects'].append(item['copy'])
 assert plan['limits']==dict(attempts=8,lean_seconds=600,heap_mib=8192,threads=1,max_heartbeats=300000,max_rec_depth=4096,all_bytes=134217728,metadata_bytes=16777216)
 assert plan['pressure_limits']['one_host_one_heavy'] and plan['pressure_limits']['owned_job_memory_and_rss_bytes']==12*1024**3
 for filename,sha in [('execute_bounded.py','32e3856ab841004a8485435e423cac3ae407d84da227b44750ca7ce803ceda9c'),('outer-supervisor.py','48bef472d962d86137ff9d34f93cc13f49a1b21c5a1175be9782707fa8d3af86')]:assert hashlib.sha256((meta/filename).read_bytes()).hexdigest()==sha
 policy=load(meta/'memory-policy.json');assert policy['heap_mib']==8192 and policy['threads']==1
 assert policy['outer_pressure_stop_free_ram_mib']==1536 and policy['outer_pressure_stop_commit_headroom_mib']==1024 and policy['outer_whole_group_private_commit_max_mib']==10240
 assert len(plan['targets'])==1;t=plan['targets'][0];assert t['module']==name
 source=checked(saved/'source/ShielddSecurity'/(name+'.lean'),t['source']);assert source==(packet/'source/ShielddSecurity'/(name+'.lean')).read_bytes();sources[name]=source
 assert re.findall(r'(?m)^import ([\w.]+)\s*$',source.decode())==t['imports']
 for dep in t['imports']:assert dep.removeprefix('ShielddSecurity.')in owned if dep.startswith('ShielddSecurity.')else dep in external['modules'],dep
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|extern|native_decide|run_tac|initialize|ofReduceBool|skipKernelTC)\b',source.decode())
 old=checked(repo/record['old_source']['path'],record['old_source']).decode().replace('\r\n','\n')
 if name=='TransferBlstArmInverseFactors01':
  for term in ['s.a','s.b']:
   old=old.replace(f'_ = 2*(scale*({term}:Int)) := by simp only [Int.mul_assoc, Int.mul_add]',f'_ = 2*(scale*({term}:Int)) := by simp only [Int.mul_assoc]')
 if name=='TransferBlstArmInverseApproxBits01':old=old.replace('Nat.mul_mod_left,Nat.zero_mod,Nat.zero_add','Nat.mul_mod_left,Nat.zero_add')
 if name=='TransferBlstArmInverseNorm01':
  old='import Mathlib.Algebra.Group.Nat.Defs\n'+old
  old=old.replace('by rw [pow_succ]; ring','by rw [Nat.pow_succ]; simp only [Nat.mul_assoc]').replace('_ = inputBound*(f.natAbs+g.natAbs) := by ring','_ = inputBound*(f.natAbs+g.natAbs) := by rw [Nat.mul_add]')
 if name=='TransferBlstArmInverseApproxError01':
  old='import Mathlib.Algebra.Group.Nat.Defs\n'+old
  old=old.replace('2^shift*(low.toNat%2147483648) := by ring','2^shift*(low.toNat%2147483648) := by simp only [Nat.mul_add, Nat.mul_comm, Nat.add_assoc, Nat.add_comm]')
  old=old.replace('_ = scale*(quotient+1) := by ring','_ = scale*(quotient+1) := by simp only [Nat.mul_add] <;> omega').replace('rw [scale,←pow_add]','rw [scale,←Nat.pow_add]')
 if name=='TransferBlstArmInverseApproxInput01':
  old=old.replace('import ShielddSecurity.TransferBlstArmInverseApproxBits01\n','import ShielddSecurity.TransferBlstArmInverseApproxBits01\nimport Mathlib.Algebra.Ring.Int.Defs\nimport Mathlib.Data.Nat.Cast.Basic\nimport ShielddSecurity.TransferScalarWordPrimitives01\nimport ShielddSecurity.TransferScalarSerializationRange01\n')
  old=old.replace('    _ = _ := by ring','    _ = _ := by\n      have factor : (2147483648 : Nat) * 8589934592 = 18446744073709551616 := by decide +kernel\n      rw [Nat.mul_add, ←factor, Nat.mul_assoc, Nat.add_assoc]')
  old=old.replace('simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using cast','simpa only [Int.natCast_add,Int.natCast_mul] using cast').replace('\n  ring\n','\n  omega\n')
 if name=='TransferBlstArmInverseApproxRows01':
  old=old.replace('import ShielddSecurity.TransferBlstArmInverseApproxInput01\n','import ShielddSecurity.TransferBlstArmInverseApproxInput01\nimport ShielddSecurity.TransferBlstArmInverseFactors01\n')
  for i in [0,1]:
   old=old.replace(f'_ = (s.f{i}*(approxA:Int)+s.g{i}*(approxB:Int))+scale*(s.f{i}*deltaA+s.g{i}*deltaB) := by ring',f'_ = (s.f{i}*(approxA:Int)+s.g{i}*(approxB:Int))+scale*(s.f{i}*deltaA+s.g{i}*deltaB) := by\n        simp only [Int.mul_add, Int.mul_left_comm, Int.add_assoc, Int.add_left_comm, Int.add_comm]')
   old=old.replace(f'by rw [← tracked.{i+1}]; ring',f'by rw [← tracked.{i+1}]; simp only [Int.mul_add, Int.add_assoc]')
 if name=='TransferBlstArmInversePrefixDiv01':
  old=old.replace('by rw [pow_add]','by rw [Int.pow_add]').replace('\n  ring\n','\n  rw [Int.mul_assoc]\n')
 if name=='TransferBlstArmInverseErrorRows01':
  old=old.replace('_ = ((2:Int)^count)*actual-scale*(((2:Int)^count)*approx) := by ring','_ = ((2:Int)^count)*actual-scale*(((2:Int)^count)*approx) := by simp only [Int.mul_sub, Int.mul_left_comm]')
  old=old.replace('_ = _ := by rw [actualRow,approxRow]; ring','_ = _ := by\n        rw [actualRow,approxRow,Int.sub_mul,Int.sub_mul,Int.mul_add]\n        simp only [Int.mul_comm, Int.mul_left_comm]\n        omega')
 if name=='TransferBlstArmInverseWindowPrefix01':
  old=old.replace('import ShielddSecurity.TransferBlstArmInverseWindowSelect01\n','import ShielddSecurity.TransferBlstArmInverseWindowSelect01\nimport Mathlib.Tactic.Ring.Basic\n')
  old=old.replace('Nat.mul_zero, add_zero, pow_two]\n    ring','Nat.mul_zero, Nat.add_zero, Nat.pow_two]\n    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm]')
  old=old.replace('Nat.mul_zero, add_zero]\n    ring','Nat.mul_zero, Nat.add_zero]\n    ring1').replace('not_ne_iff.mp','Classical.not_not.mp').replace('simpa only [one_mul, add_zero]','simpa only [Nat.one_mul, Nat.add_zero]')
 if name=='TransferBlstArmInverseWindowJoint01':old=old.replace('not_ne_iff.mp','Classical.not_not.mp')
 if name in ['TransferBlstArmInverseFactors01','TransferBlstArmInverseApproxBits01']:
  old=old.replace('#check @ShielddSecurity.'+name+'.','#check @').replace('#print axioms ShielddSecurity.'+name+'.','#print axioms ')
 assert old==source.decode().replace('\r\n','\n'),name
 prior_reports=json.loads(checked(repo/record['baseline']['path'],record['baseline']))['complete_types_and_axioms']
 baseline={x['name']:{k:x[k]for k in ['axioms','full_type_sha256']}for x in prior_reports if x['name']in t['audit_names']}
 assert len(baseline)==len(t['audit_names']) and baseline==load(meta/'baseline-type-axiom-review.json')['expected_reports']
 events=[json.loads(x)for x in (packet/'events.jsonl').read_text().splitlines()];assert len(events)==2
 start,finish=events;assert start['event']=='attempt_started' and finish['event']=='attempt_finished' and start['module']==finish['module']==name and start['attempt']==finish['attempt']==1
 result=finish['result'];assert result['status']=='passed' and result['seconds']<240 and result['peak_rss_bytes']<12*1024**3
 seconds+=result['seconds'];command=result['command'];assert '-j1'in command and '-M8192'in command and command[-1]==t['source']['path'] and '-DmaxHeartbeats=300000'in command and '-DmaxRecDepth=4096'in command
 raw=checked(packet/'receipts'/(name+'.full-types-and-axioms.txt'),result['stdout']);left=raw.decode();assert not re.search(r'(?im)^.*(?:warning|error|panic):|sorryAx|uncaught exception|internal exception',left)
 checks=re.findall(r'(?m)^#check @([\w.]+)\s*$',source.decode());assert checks==re.findall(r'(?m)^#print axioms ([\w.]+)\s*$',source.decode())
 namespace=re.search(r'(?m)^namespace ([\w.]+)',source.decode()).group(1);checks=[x if x.startswith('ShielddSecurity.')else namespace+'.'+x for x in checks];assert checks==t['audit_names'] and set(checks)==set(result['audits'])
 for declaration in checks:
  pattern=r'^@?'+re.escape(declaration)+r'(?:\.\{[^}\n]*\})?\s*:[\s\S]*?^\''+re.escape(declaration)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$"
  matches=list(re.finditer(pattern,left,re.M));assert len(matches)==1,declaration;m=matches[0]
  full=m.group(0).split("\n'"+declaration+"'",1)[0].strip();axioms=[]if m.group(1)is None else[x.strip()for x in m.group(1).split(',')]
  actual=dict(axioms=axioms,full_type_sha256=hashlib.sha256(full.encode()).hexdigest());assert actual==result['audits'][declaration]==baseline[declaration],declaration
  assert set(axioms)<={'propext','Quot.sound','Classical.choice'}
  reports.append(dict(name=declaration,full_type=full,**actual));left=left[:m.start()]+left[m.end():]
 assert not left.strip();modules[name]=dict(source=ident(source),audits=len(checks),seconds=result['seconds'],peak_rss_bytes=result['peak_rss_bytes'],report=ident(raw),objects=result['objects']);owned[name]=modules[name]
 packets.append(dict(packet=record['packet'],manifest=record['manifest'],external_modules=len(external['modules']),external_file_identities=len(external['immutable_files']),owned_imports=len(floor['selected'])))
assert len(modules)==10 and len(reports)==44
pending=out.with_name(out.name+'.pending');assert not pending.exists();pending.mkdir()
for name,b in sources.items():p=pending/'source/ShielddSecurity'/(name+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
evidence=dict(status='passed',runtime_sha=review['runtime_sha'],transport_commit=review['transport_commit'],modules=modules,reports=len(reports),complete_types_and_axioms=reports,independent_baseline_matches=len(reports),packets=packets,legacy_owned_objects_reused=False,source_contracts_unchanged=True,seconds=seconds,scope=review['scope'],baseline_review=ident((root/'baseline-review.json').read_bytes()),refresh=ident(Path(__file__).read_bytes()),full_transfer='OPEN',native_credit=0,new_cumulative_credit=0,certification=False)
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,out)
print(json.dumps({k:evidence[k]for k in ['status','reports','independent_baseline_matches','seconds','new_cumulative_credit']}))
