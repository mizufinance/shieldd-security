from pathlib import Path
import argparse,json,hashlib,subprocess,re,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--batch',type=Path,required=True);ap.add_argument('--runtime',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();pending.mkdir()
c=json.loads((root/'config.json').read_text());verified={}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def checked(r):
 p=Path(r['path']);stamp=(p.stat().st_size,p.stat().st_mtime_ns)
 if verified.get(r['path'])==(stamp,r):return
 assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],r['path'];verified[r['path']]=(stamp,r)
assert c['guard_sha256']=='cb3e8db951d4b6ddaf0ed0555ba3e0db15441daf3ea232273b6401f43a7faff2'
assert subprocess.check_output(['git','-C',str(a.runtime),'rev-parse','HEAD'],text=True).strip()==c['runtime_sha'];assert not subprocess.check_output(['git','-C',str(a.runtime),'status','--porcelain'])
prior={};prior_files=['inverse-factors/evidence.json','inverse-batch/qualified/evidence.json']
for file in prior_files:
 e=json.loads((root.parent/file).read_text());assert e['status']=='passed' and e['runtime_sha']==c['runtime_sha'] and not e['certification'];prior.update({x['name']:x for x in e['complete_types_and_axioms']})
inherited=json.loads((root.parent/'low31-gap-mac/qualified/evidence.json').read_text());assert inherited['status']=='passed' and inherited['native_credit']==0 and inherited['runtime_sha']==c['runtime_sha']
assert sha(root/'transport-manifest.json')==c['transport_manifest_sha256'];transport=json.loads((root/'transport-manifest.json').read_text());assert transport['status']=='UNVERIFIED_SOURCE_ONLY' and transport['kernel_receipt'] is None
new_name=c['root'];target=next(x for x in transport['targets'] if x['module']=='ShielddSecurity.'+new_name);assert target['sha256']==c['sources'][new_name]['original_sha256']
for name,r in c['sources'].items():
 old=root/'original-source'/(name+'.lean');new=root/'source/ShielddSecurity'/(name+'.lean');assert sha(old)==r['original_sha256'] and sha(new)==r['variant_sha256']
 def definitions(p):
  text=p.read_text();return {m[1]:m[0].strip() for m in re.finditer(r'^(?:structure|def) (\w+)[\s\S]*?(?=^(?:structure|def|theorem) |\Z)',text,re.M)}
 assert definitions(old)==definitions(new),name
 if name==new_name:
  append=''.join('\nset_option pp.all true in\n#check @ShielddSecurity.'+name+'.'+d+'\n#print axioms ShielddSecurity.'+name+'.'+d+'\n' for d in target['declarations'])
  assert new.read_bytes()==old.read_bytes()+append.encode()
completion=json.loads((a.batch/'completion.json').read_text());assert completion['status']=='passed' and completion['root']==new_name;checked(completion['dependency_manifest']);plan=json.loads(Path(completion['dependency_manifest']['path']).read_text());assert plan['runtime_sha']==c['runtime_sha'] and plan['mathlib']==c['mathlib']
limits=dict(threads=1,default_heap_MiB=1536,elliptic_point_closure_heap_MiB=1536,rss_bytes=4*1024**3,module_seconds=240,heartbeats=900000,recDepth=8192,free_memory_percent=15,free_disk_bytes=2*1024**3);assert plan['limits']==limits
for r in completion['final_files'].values():checked(r)
assert any(r['sha256']==c['guard_sha256'] for r in completion['final_files'].values())
bfxil='TransferBlstArmInverseWindowBfxil01';assert set(plan['selected'])==set(c['sources'])|{bfxil};assert set(plan['order'])==set(c['sources']);assert [x['module'] for x in completion['completed']]==plan['order']
for name,row in plan['selected'].items():
 checked(row['source']);expected=c['sources'][name]['variant_sha256'] if name in c['sources'] else inherited['modules'][name]['source_sha256'];assert row['source']['sha256']==expected;assert row['heap_MiB']==1536
 assert all(not n.startswith('ShielddSecurity.') or n.removeprefix('ShielddSecurity.') in plan['selected'] for n in row['imports'])
modules={};reports=[];replayed=0;new_reports=0
for item in completion['completed']:
 assert item['status']=='passed';checked(item['receipt']);r=json.loads(Path(item['receipt']['path']).read_text());name=r['module'];assert r['status']=='passed' and r['exit']==0 and r['stop'] is None and r['audit_error'] is None;assert r['dependency_manifest']==completion['dependency_manifest'];assert r['source']==plan['selected'][name]['source']
 assert '-j1' in r['command'] and '-M1536' in r['command'];assert r['seconds']<=240 and r['peak_group_rss_bytes']<=4*1024**3
 assert all(s['free_memory_percent']>=15 and s['free_disk_bytes']>=2*1024**3 for s in r['samples'])
 for k in ['source','stdout','stderr']:checked(r[k])
 assert not Path(r['stderr']['path']).read_bytes().strip()
 expected=re.findall(r'^#check @([A-Za-z0-9_.]+)\s*$',Path(r['source']['path']).read_text(),re.M);assert [x['name'] for x in r['audits']]==expected
 for report in r['audits']:
  assert set(report['axioms'])<={'propext','Quot.sound','Classical.choice'};assert hashlib.sha256(report['full_type'].encode()).hexdigest()==report['full_type_sha256']
  if name!=new_name:
   previous=prior[report['name']];assert report['full_type_sha256']==previous['full_type_sha256'] and set(report['axioms'])==set(previous['axioms']);replayed+=1
  else:new_reports+=1
 for identity in r['objects'].values():checked(identity)
 modules[name]=dict(source_sha256=r['source']['sha256'],receipt_sha256=item['receipt']['sha256'],object_sha256=r['objects']['.olean']['sha256'],reports=len(r['audits']),seconds=r['seconds'],peak_group_rss_bytes=r['peak_group_rss_bytes']);reports+=r['audits']
assert len(modules)==3 and replayed==11 and new_reports==2
result=dict(status='passed',runtime_sha=c['runtime_sha'],mathlib=c['mathlib'],scope=c['scope'],transport_commit=c['transport_commit'],native_credit=0,certification=False,full_transfer='OPEN',compiled_execution='OPEN',native_consequence='OPEN',modules=modules,reports=len(reports),existing_reports_replayed=replayed,new_bridge_reports=new_reports,complete_types_and_axioms=reports,limits=limits,guard_sha256=c['guard_sha256'],refresh_sha256=sha(Path(__file__)),dependency_manifest_sha256=completion['dependency_manifest']['sha256'],prior_evidence={f:sha(root.parent/f) for f in prior_files+['low31-gap-mac/qualified/evidence.json']})
(pending/'evidence.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');os.replace(pending,a.output);print(json.dumps(dict(status='passed',modules=3,reports=len(reports),new_bridge_reports=new_reports)))
