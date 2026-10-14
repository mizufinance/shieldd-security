from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,tarfile
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--batch',type=Path,action='append',required=True);ap.add_argument('--runtime',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();pending.mkdir()
config=json.loads((root/'config.json').read_text());verified={}
def pin(p):
 p=Path(p);return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
def checked(r):
 p=Path(r['path']);stamp=(p.stat().st_size,p.stat().st_mtime_ns)
 if verified.get(r['path'])==(stamp,r):return
 assert pin(p)==r,r['path'];verified[r['path']]=(stamp,r)
# The original guard is authenticated in every completed batch's checked final_files.
assert config['guard_sha256']=='cb3e8db951d4b6ddaf0ed0555ba3e0db15441daf3ea232273b6401f43a7faff2'
assert subprocess.check_output(['git','-C',str(a.runtime),'rev-parse','HEAD'],text=True).strip()==config['runtime_sha']
assert not subprocess.check_output(['git','-C',str(a.runtime),'status','--porcelain'])
prior=root.parent/'inverse-window-producer/qualified/evidence.json';inherited=json.loads(prior.read_text());assert inherited['status']=='passed' and inherited['runtime_sha']==config['runtime_sha'] and inherited['native_credit']==0
required={p.stem:pin(p) for p in (root/'source/ShielddSecurity').glob('*.lean')};assert set(required)==set(config['mandatory_roots'])
for name,identity in required.items():
 review=json.loads((root/'source-reviews'/(name+'.json')).read_text());assert review['transport']==config['transport_commit'];assert review['variant_source_sha256']==identity['sha256'];assert review['original_source_sha256']==pin(root/'desktop-source/ShielddSecurity'/(name+'.lean'))['sha256']
# Reconcile the draft transport and official/runtime context independently.
for name,identity in config['transport_metadata'].items():
 data=(root/name).read_bytes();assert len(data)==identity['bytes'] and hashlib.sha256(data).hexdigest()==identity['sha256']
transport=json.loads((root/'transport-manifest.json').read_text());deps=json.loads((root/'source-dependency-identities.json').read_text());review=json.loads((root/'transport-review.json').read_text())
assert transport['status']=='UNVERIFIED_SOURCE_ONLY' and transport['kernel_receipt'] is None and transport['fresh_audits']==0
assert review['transport']==config['transport_commit'] and review['official_source_identities_verified']==len(deps['external_sources'])==983
for entry in deps['owned']:
 name=entry['module'].removeprefix('ShielddSecurity.');raw=(root/'desktop-source/ShielddSecurity'/(name+'.lean')).read_bytes()
 assert len(raw)==entry['bytes'] and hashlib.sha256(raw).hexdigest()==entry['sha256']
 appended=''.join('\nset_option pp.all true in\n#check @'+entry['module']+'.'+decl+'\n#print axioms '+entry['module']+'.'+decl+'\n' for decl in entry['declarations']).encode()
 source_review=json.loads((root/'source-reviews'/(name+'.json')).read_text())
 expected=raw.decode()
 repairs=source_review.get('proof_repairs',[])
 if name=='TransferBlstArmInverseWindowBfxil01':
  assert repairs==[{'before':'UInt64.toNat_ofBitVec, BitVec.toNat_append','after':'UInt64.toNat_ofBitVec, BitVec.append_eq, BitVec.toNat_append'},{'before':'Nat.mul_mod_left, zero_add, Nat.mod_mod','after':'Nat.mul_mod_left, Nat.zero_mod, Nat.zero_add, Nat.mod_mod'}]
  assert source_review['audit_append_only'] is False
 else:
  assert not repairs and source_review['audit_append_only'] is True
 for repair in repairs:
  assert expected.count(repair['before'])==1
  expected=expected.replace(repair['before'],repair['after'])
 assert (root/'source/ShielddSecurity'/(name+'.lean')).read_bytes()==expected.encode()+appended
chain=Path.home()/'.elan/toolchains/leanprover--lean4---v4.30.0'
for entry in deps['external_sources']:
 data=(chain/entry['toolchain_relative_path']).read_bytes();assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256']
contexts={entry['member']:entry for entry in transport['members'] if entry['member'].startswith('context/')}
assert set(contexts)==set(review['independently_matched_contexts'])
archive=next((Path.home()/'.cargo/registry/cache').glob('*/blst-0.3.17.crate'))
assert hashlib.sha256(archive.read_bytes()).hexdigest()==config['locked_archive_sha256']
with tarfile.open(archive) as bundle:
 for name,target in review['independently_matched_contexts'].items():
  data=bundle.extractfile(target).read() if target.startswith('blst-0.3.17/') else (a.runtime/target).read_bytes()
  assert len(data)==contexts[name]['bytes'] and hashlib.sha256(data).hexdigest()==contexts[name]['sha256']

modules={};reports=[];plans=[];roots=[];official_names=set()
limits=dict(threads=1,default_heap_MiB=1536,elliptic_point_closure_heap_MiB=1536,rss_bytes=4*1024**3,module_seconds=240,heartbeats=900000,recDepth=8192,free_memory_percent=15,free_disk_bytes=2*1024**3)
for batch in a.batch:
 completion=json.loads((batch/'completion.json').read_text());assert completion['status']=='passed';roots.append(completion['root']);checked(completion['dependency_manifest']);plan=json.loads(Path(completion['dependency_manifest']['path']).read_text());assert plan['runtime_sha']==config['runtime_sha'] and plan['mathlib']==config['mathlib'] and plan['limits']==limits
 official_names.update(plan['official_modules'])
 assert any(r['sha256']==config['guard_sha256'] for r in completion['final_files'].values())
 for r in completion['final_files'].values():checked(r)
 assert set(plan['selected'])<=set(required)
 for name,row in plan['selected'].items():
  checked(row['source']);assert row['source']['sha256']==required[name]['sha256'];assert row['heap_MiB']==1536
  assert all(not n.startswith('ShielddSecurity.') or n.removeprefix('ShielddSecurity.') in required for n in row['imports'])
 assert [e['module'] for e in completion['completed']]==plan['order']
 for item in completion['completed']:
  assert item['status']=='passed';checked(item['receipt']);r=json.loads(Path(item['receipt']['path']).read_text());name=r['module'];assert r['status']=='passed' and r['exit']==0 and r['stop'] is None and r['audit_error'] is None
  assert r['dependency_manifest']==completion['dependency_manifest'];assert r['source']==plan['selected'][name]['source'];assert '-M1536' in r['command'] and '-j1' in r['command']
  for key in ['source','stdout','stderr']:checked(r[key])
  assert not Path(r['stderr']['path']).read_bytes().strip();assert r['seconds']<=240 and r['peak_group_rss_bytes']<=4*1024**3
  assert all(s['free_memory_percent']>=15 and s['free_disk_bytes']>=2*1024**3 for s in r['samples'])
  source=Path(r['source']['path']).read_text();expected=re.findall(r'(?m)^#check @([A-Za-z0-9_.]+)\s*$',source);assert [d['name'] for d in r['audits']]==expected
  declared=re.findall(r'(?m)^(?:theorem|def|structure) ([A-Za-z0-9_]+)',source);assert set(expected)=={'ShielddSecurity.'+name+'.'+d for d in declared}
  for d in r['audits']:
   assert set(d['axioms'])<={'propext','Quot.sound','Classical.choice'};assert hashlib.sha256(d['full_type'].encode()).hexdigest()==d['full_type_sha256']
  for identity in r['objects'].values():checked(identity)
  assert name not in modules
  modules[name]=dict(source_sha256=r['source']['sha256'],receipt_sha256=item['receipt']['sha256'],object_sha256=r['objects']['.olean']['sha256'],reports=len(r['audits']),seconds=r['seconds'],peak_group_rss_bytes=r['peak_group_rss_bytes']);reports+=r['audits']
 plans.append(dict(root=plan['root'],dependency_manifest_sha256=completion['dependency_manifest']['sha256'],selected=len(plan['selected']),replayed=len(plan['order'])))
assert set(roots)==set(required)==set(modules)
assert official_names=={r['module'] for r in deps['external_sources']}
evidence=dict(status='passed',runtime_sha=config['runtime_sha'],mathlib=config['mathlib'],scope=config['scope'],transport_commit=config['transport_commit'],native_credit=0,certification=False,full_transfer='OPEN',native_consequence='OPEN',compiled_execution='OPEN',limits=limits,modules=modules,reports=len(reports),complete_types_and_axioms=reports,batches=plans,guard_sha256=config['guard_sha256'],refresh_sha256=pin(Path(__file__))['sha256'],prior_evidence_sha256=pin(prior)['sha256'])
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,a.output);print(json.dumps(dict(status='passed',modules=len(modules),reports=len(reports))))
