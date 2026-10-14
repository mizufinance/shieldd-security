"""Reconcile an isolated packing-owner replay against accepted original contracts."""
from pathlib import Path
import argparse,hashlib,json,os,re,tarfile,zlib
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--repository',type=Path,required=True);ap.add_argument('--reports-root',type=Path,required=True);ap.add_argument('--official-archive',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
repo=a.repository.resolve();packet=a.reports_root.resolve();out=a.output.resolve();assert not out.exists()
def ident(b):return dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def checked(p,record):
 b=p.read_bytes();assert ident(b)=={k:record[k] for k in ['bytes','sha256']},str(p);return b
def load(p):return json.loads(p.read_bytes())
review=load(root/'baseline-review.json');manifest=json.loads(checked(root/'successful-manifest.json',review['packet_manifest']));assert checked(packet/'manifest.json',review['packet_manifest'])==(root/'successful-manifest.json').read_bytes()
assert manifest['exact_runtime_sha']==review['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
assert manifest['certification'] is False and manifest['native_credit']==0 and manifest['new_cumulative_credit']==0 and not manifest['legacy_owned_objects_reused']
prefix=Path('variants/transfer-packing-owner-replay-20261014-05')
for item in manifest['members']:checked(packet/Path(item['member']).relative_to(prefix),item)
meta=packet/'original-metadata'
for item in manifest['archive_members']:checked(meta/item['member'],item)
plan=load(meta/'plan.json');external=load(meta/'external-floor.json');oldfloor=None
with tarfile.open(a.official_archive) as archive:
 b=archive.extractfile('original/transfer-external-floor-complete-20261010-08/external-floor.json').read()
 assert ident(b)==review['external_parent'];oldfloor=json.loads(b)
assert external['parent_floor_identity']['sha256']==review['external_parent']['sha256']
assert external['admission_ready'] and not external['gaps']
for n,r in external['modules'].items():assert oldfloor['modules'][n]==r,n
oldpins={(r['path'],r['bytes'],r['sha256']) for r in oldfloor['immutable_files']}
assert all((r['path'],r['bytes'],r['sha256']) in oldpins for r in external['immutable_files'])
assert plan['owned_imports']==[]
floor=load(meta/'owned-floor/composition-review.json');assert floor['admission_ready'] and floor['kernel_credit']==0 and floor['selected']==[]
assert ident((meta/'external-floor.json').read_bytes())=={k:plan['external_floor'][k] for k in ['bytes','sha256']}
assert plan['limits']==dict(attempts=8,lean_seconds=600,heap_mib=8192,threads=1,max_heartbeats=300000,max_rec_depth=4096,all_bytes=134217728,metadata_bytes=16777216)
assert plan['pressure_limits']['one_host_one_heavy'] and plan['pressure_limits']['owned_job_memory_and_rss_bytes']==12*1024**3
for filename,sha in [('execute_bounded.py','32e3856ab841004a8485435e423cac3ae407d84da227b44750ca7ce803ceda9c'),('outer-supervisor.py','48bef472d962d86137ff9d34f93cc13f49a1b21c5a1175be9782707fa8d3af86')]:
 assert hashlib.sha256((meta/filename).read_bytes()).hexdigest()==sha
 assert (root/'resource-profile'/filename).read_bytes()==(meta/filename).read_bytes()
policy=load(meta/'memory-policy.json');assert policy['heap_mib']==8192 and policy['threads']==1
assert policy['outer_pressure_stop_free_ram_mib']==1536 and policy['outer_pressure_stop_commit_headroom_mib']==1024
assert policy['outer_whole_group_private_commit_max_mib']==10240
sources={};targets={x['module']:x for x in plan['targets']};assert list(targets)==manifest['owned_modules'] and len(targets)==8
for name,t in targets.items():
 raw=checked(root/'source/ShielddSecurity'/(name+'.lean'),t['source']);assert raw==(packet/'source/ShielddSecurity'/(name+'.lean')).read_bytes();sources[name]=raw
 assert re.findall(r'(?m)^import ([\w.]+)\s*$',raw.decode())==t['imports']
 for dep in t['imports']:assert dep.removeprefix('ShielddSecurity.') in targets if dep.startswith('ShielddSecurity.') else dep in external['modules'],dep
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|extern|native_decide|run_tac|initialize|ofReduceBool|skipKernelTC)\b',raw.decode())
# Exact source repairs reviewed against original published modules. Preserve all
# definition bodies and theorem statements; permit only these proof/import edits.
for name,record in review['old_sources'].items():
 old=checked(repo/record['path'],record).decode().replace('\r\n','\n')
 if name=='TransferBoundedNativeCodec01':
  declaration=re.search(r'(?m)^def nullifierModulus : Nat := [0-9]+$',old).group(0)
  assert declaration in sources['TransferNullifierModulus01'].decode();continue
 if name=='TransferScalarSerializationRange01':old=old.replace('import ShielddSecurity.TransferNativeOnlyPublication01','import ShielddSecurity.TransferNullifierModulus01\nimport Init.Data.Nat.Div.Lemmas\nimport Init.Data.List.Lemmas')
 if name=='TransferBlstArmInverseWindowArithmetic01':
  old=old.replace('import Mathlib.Tactic.Ring','import Init.Data.Nat.Div.Lemmas\nimport Mathlib.Algebra.Group.Nat.Defs').replace('Nat.div_eq_of_lt bounded, zero_add]','Nat.div_eq_of_lt bounded, Nat.zero_add]').replace('    ring\n','    rw [Nat.mul_assoc, Nat.mul_left_comm scale divisor high, Nat.add_comm]\n')
 if name=='TransferBlstArmInverseWindowAlign01':old=old.replace('← pow_add','← Nat.pow_add')
 if name=='TransferBlstArmInverseWindowClz01':old=old.replace('[pow_zero, one_mul, Nat.sub_zero,','[Nat.pow_zero, Nat.one_mul, Nat.sub_zero,').replace('lowB.toNat_lt, add_zero]','lowB.toNat_lt, Nat.add_zero]')
 if name=='TransferBlstArmInverseWindowSelect01':old=old.replace('UInt64.toNat_zero, Nat.mul_zero, add_zero]','UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]')
 assert old==sources[name].decode().replace('\r\n','\n'),name
baseline={};files={}
for name,record in review['baselines'].items():
 path=record['path']
 if path not in files:
  raw=checked(repo/path,record);files[path]=json.loads(zlib.decompress(raw) if path.endswith('.zlib') else raw)
 d=files[path]
 if record['kind']=='cached_reports':prior=d['reports'][name]
 else:prior=next(x for x in d['complete_types_and_axioms'] if x['name']==name)
 baseline[name]={k:prior[k] for k in ['axioms','full_type_sha256']}
assert baseline==load(meta/'baseline-type-axiom-review.json')['expected_reports'] and len(baseline)==50
raw_events=(packet/'events.jsonl').read_bytes();events=[json.loads(x) for x in raw_events.decode().splitlines()];assert len(events)==16
reports=[];modules={};seen=set();seconds=0
for i,(name,t) in enumerate(targets.items(),1):
 start,finish=events[2*(i-1):2*i];assert start['event']=='attempt_started' and finish['event']=='attempt_finished'
 assert start['module']==finish['module']==name and start['attempt']==finish['attempt']==i
 result=finish['result'];assert result['status']=='passed' and result['seconds']<240 and result['peak_rss_bytes']<12*1024**3
 seconds+=result['seconds'];command=result['command'];assert '-j1' in command and '-M8192' in command
 assert command[-1]==t['source']['path'] and '-DmaxHeartbeats=300000' in command and '-DmaxRecDepth=4096' in command
 raw=checked(packet/'receipts'/(name+'.full-types-and-axioms.txt'),result['stdout']);left=raw.decode();assert not re.search(r'(?im)^.*(?:warning|error|panic):|sorryAx|uncaught exception|internal exception',left)
 source=sources[name].decode();checks=re.findall(r'(?m)^#check @([\w.]+)\s*$',source);assert checks==re.findall(r'(?m)^#print axioms ([\w.]+)\s*$',source)
 namespace=re.search(r'(?m)^namespace ([\w.]+)',source).group(1);checks=[x if x.startswith('ShielddSecurity.') else namespace+'.'+x for x in checks]
 assert checks==t['audit_names'] and set(checks)==set(result['audits'])
 for declaration in checks:
  assert declaration not in seen;seen.add(declaration)
  pattern=r'^@?'+re.escape(declaration)+r'(?:\.\{[^}\n]*\})?\s*:[\s\S]*?^\''+re.escape(declaration)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$"
  matches=list(re.finditer(pattern,left,re.M));assert len(matches)==1,declaration;m=matches[0]
  full=m.group(0).split("\n'"+declaration+"'",1)[0].strip();axioms=[] if m.group(1) is None else [x.strip() for x in m.group(1).split(',')]
  actual=dict(axioms=axioms,full_type_sha256=hashlib.sha256(full.encode()).hexdigest());assert actual==result['audits'][declaration]==baseline[declaration],declaration
  assert set(axioms)<={'propext','Quot.sound','Classical.choice'}
  reports.append(dict(name=declaration,full_type=full,**actual));left=left[:m.start()]+left[m.end():]
 assert not left.strip();modules[name]=dict(source=ident(sources[name]),audits=len(checks),seconds=result['seconds'],peak_rss_bytes=result['peak_rss_bytes'],report=ident(raw),objects=result['objects'])
assert seen==set(baseline) and seconds<600
pending=out.with_name(out.name+'.pending');assert not pending.exists();pending.mkdir()
for name,b in sources.items():p=pending/'source/ShielddSecurity'/(name+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
evidence=dict(status='passed',runtime_sha=review['runtime_sha'],transport_commit=review['transport_commit'],modules=modules,reports=len(reports),complete_types_and_axioms=reports,independent_baseline_matches=len(seen),external_modules_verified=len(external['modules']),external_file_identities_verified=len(external['immutable_files']),legacy_owned_objects_reused=False,source_contracts_unchanged=True,seconds=seconds,scope=review['scope'],manifest=ident((root/'successful-manifest.json').read_bytes()),baseline_review=ident((root/'baseline-review.json').read_bytes()),refresh=ident(Path(__file__).read_bytes()),full_transfer='OPEN',native_credit=0,new_cumulative_credit=0,certification=False)
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,out);print(json.dumps({k:evidence[k] for k in ['status','reports','independent_baseline_matches','external_modules_verified','external_file_identities_verified','seconds','new_cumulative_credit']}))
