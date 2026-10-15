"""Atomically reconcile original successful source-model receipts; no native credit."""
from pathlib import Path
import argparse,hashlib,json,os,re
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--repository',type=Path,required=True);ap.add_argument('--reports-root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists()
def ident(data):return {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
def checked(path,r):
 data=path.read_bytes();assert ident(data)=={k:r[k] for k in ['bytes','sha256']},str(path);return data
manifest=json.loads((root/'successful-manifest.json').read_text());mapping=json.loads((root/'dependency-repository-review.json').read_text());assert not mapping['missing'];assert manifest['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a';assert not manifest['certification'] and manifest['native_credit']==0
repo=a.repository.resolve();packet=a.reports_root.resolve();sources={}
for dep in manifest['dependencies']:
 item=mapping['matched'][dep['module']];data=checked(repo/item['path'],item)
 if ident(data)!={k:dep[k] for k in ['bytes','sha256']}:
  lf=data.replace(b'\r\n',b'\n');variants=[lf,lf.replace(b'\n',b'\r\n')];data=next(v for v in variants if ident(v)=={k:dep[k] for k in ['bytes','sha256']})
 sources[dep['module']]=data
binding=json.loads((root/'runtime-binding-review.json').read_text());assert binding['runtime_sha']==manifest['runtime_sha'] and len(binding['independently_matched'])==1 and binding['native_credit']==0 and binding['certification'] is False
profile=json.loads((root/'resource-profile/expanded-memory-policy.json').read_text())
assert profile['heap_mib']==8192 and profile['inner_job_memory_and_rss_mib']==12288
assert profile['outer_whole_group_private_commit_max_mib']==10240 and profile['outer_pressure_stop_free_ram_mib']==1536 and profile['outer_pressure_stop_commit_headroom_mib']==1024
assert profile['per_lean_wall_seconds']==240 and profile['threads']==1 and not profile['old_plans_runners_and_executing_runs_modified']
review=json.loads((root/'resource-profile/memory-profile-review.json').read_text())
assert review['normative_memory_profile']==profile and not review['this_plan_modified_after_freeze']
assert hashlib.sha256((root/'resource-profile/execute_bounded.py').read_bytes()).hexdigest()==profile['runner_sha256']=='32e3856ab841004a8485435e423cac3ae407d84da227b44750ca7ce803ceda9c'
assert ident((root/'resource-profile/outer-supervisor.py').read_bytes())=={k:review['outer_supervisor_identity'][k] for k in ['bytes','sha256']}
assert profile['outer_supervisor_sha256']=='48bef472d962d86137ff9d34f93cc13f49a1b21c5a1175be9782707fa8d3af86'
assert hashlib.sha256((root/'resource-profile/outer-supervisor.py').read_bytes()).hexdigest()==profile['outer_supervisor_sha256']
assert profile['outer_effective_limit']=='min(maximum, current_owned_commit + min(freeRAM-1536MiB, commitHeadroom-1024MiB))'
assert profile['stable_admission_seconds']==60 and profile['whole_lean_seconds']==600 and profile['whole_lifecycle_wall_seconds']==1800

provenance=json.loads((root/'object-provenance-inputs.json').read_text());owned={}
for r in provenance['prior_evidence']:
 e=json.loads(checked(repo/r['path'],r));assert e['status']=='passed' and e['runtime_sha']==manifest['runtime_sha']
 owned.update(e['modules'])
assert len(owned)==57
external_manifest=json.loads(checked(repo/provenance['external_packet_manifest']['path'],provenance['external_packet_manifest']))
external_identity=next(r for r in external_manifest['archive_members']if r['member']=='external-floor.json')
assert {k:external_identity[k]for k in ['bytes','sha256']}==provenance['external_floor']
external=json.loads(checked(packet/'qualified-external-floor.json',provenance['external_floor']))
assert external['admission_ready'] and not external['gaps']
object_reviews={}

reports=[];results={}

for module in manifest['modules']:
 name=module['module'];src=checked(root/module['source_path'],module['source']);assert src==sources[name]
 meta=packet/'original-metadata'/name;plan_bytes=checked(meta/'plan.json',module['plan_identity']);runner=checked(meta/'execute_bounded.py',module['runner_identity'])
 assert hashlib.sha256(runner).hexdigest()=='32e3856ab841004a8485435e423cac3ae407d84da227b44750ca7ce803ceda9c'
 plan=json.loads(plan_bytes);target=next(t for t in plan['targets'] if t['module']==name);assert ident(src)=={k:target['source'][k] for k in ['bytes','sha256']}
 assert plan['limits']==dict(attempts=8,lean_seconds=600,heap_mib=8192,threads=1,max_heartbeats=300000,max_rec_depth=4096,all_bytes=134217728,metadata_bytes=16777216)
 assert len(plan['targets'])==1
 assert re.findall(r'(?m)^import ([\w.]+)\s*$',src.decode())==target['imports']
 for dep in target['imports']:assert dep.removeprefix('ShielddSecurity.')in owned if dep.startswith('ShielddSecurity.')else dep in external['modules'],dep
 assert plan['pressure_limits']['one_host_one_heavy'] and plan['pressure_limits']['owned_job_memory_and_rss_bytes']==12*1024**3

 assert {k:plan['external_floor'][k]for k in ['bytes','sha256']}==provenance['external_floor']
 pinned={(r['path'],r['bytes'],r['sha256'])for r in plan['pins']}
 assert (plan['external_floor']['path'],plan['external_floor']['bytes'],plan['external_floor']['sha256'])in pinned
 assert "records += floor['immutable_files']\n    verify(records)"in runner.decode()
 floor=json.loads(checked(meta/'owned-floor/composition-review.json',plan['owned_import_pool']))
 assert floor['admission_ready'] and floor['kernel_credit']==0 and {r['module']for r in floor['selected']}==set(owned)
 assert plan['owned_imports']==[r['copy']for r in floor['selected']]
 for r in floor['selected']:
  dep=r['module'];prior=owned[dep];identity=lambda x:{k:x[k]for k in ['bytes','sha256']}
  assert identity(r['source'])==prior['source']==ident(sources[dep]),dep
  assert any(identity(r['object'])==identity(old)for old in prior['objects']),dep
  assert identity(r['copy'])==identity(r['object']),dep
  assert (r['copy']['path'],r['copy']['bytes'],r['copy']['sha256'])in pinned,dep
 object_reviews[name]=dict(original_composition=plan['owned_import_pool'],owned_imports=len(floor['selected']),external_identity=provenance['external_floor'],external_files=len(external['immutable_files']))
 pinset={(r['bytes'],r['sha256']) for r in plan['pins']};seen=set()
 def visit(n):
  if n in seen:return
  seen.add(n);data=sources[n];assert (len(data),hashlib.sha256(data).hexdigest()) in pinset,n
  for child in re.findall(r'(?m)^import ShielddSecurity\.([A-Za-z0-9_]+)\s*$',data.decode()):visit(child)
 visit(name)
 events=[json.loads(line) for line in checked(packet/module['original_events']['path'],module['original_events']).decode().splitlines()]
 assert len(events)==2 and [e['event'] for e in events]==['attempt_started','attempt_finished']
 assert events[0]['module']==events[1]['module']==name and events[0]['attempt']==events[1]['attempt']==1
 finishes=[e['result'] for e in events if e['event']=='attempt_finished'];assert len(finishes)==1;result=finishes[0];assert result['status']=='passed' and result['seconds']<240 and result['peak_rss_bytes']<12*1024**3
 assert '-j1' in result['command'] and '-M8192' in result['command']
 assert result['command'][-1]==target['source']['path'] and '-DmaxHeartbeats=300000'in result['command'] and '-DmaxRecDepth=4096'in result['command']
 raw=checked(packet/module['full_type_axiom_report']['path'],module['full_type_axiom_report']);assert ident(raw)=={k:result['stdout'][k] for k in ['bytes','sha256']};left=raw.decode()
 assert not re.search(r'(?im)^.*(?:warning|error|panic):|sorryAx|uncaught exception|internal exception',left)
 names=re.findall(r'(?m)^#check @([\w.]+)\s*$',src.decode());assert names==re.findall(r'(?m)^#print axioms ([\w.]+)\s*$',src.decode());names=[n if n.startswith('ShielddSecurity.') else 'ShielddSecurity.'+name+'.'+n for n in names];assert names==target['audit_names'] and set(names)==set(result['audits'])
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|extern|native_decide|run_tac|initialize|ofReduceBool|skipKernelTC)\b',src.decode())
 for n in names:
  pattern=r'^@?'+re.escape(n)+r'(?:\.\{[^}\n]*\})?\s*:[\s\S]*?^\''+re.escape(n)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$";ms=list(re.finditer(pattern,left,re.M));assert len(ms)==1,n;m=ms[0];full=m.group(0).split("\n'"+n+"'",1)[0].strip();axioms=[] if m.group(1) is None else [x.strip() for x in m.group(1).split(',')];assert set(axioms)<= {'propext','Quot.sound','Classical.choice'};assert axioms==result['audits'][n]['axioms'];sha=hashlib.sha256(full.encode()).hexdigest();assert sha==result['audits'][n]['full_type_sha256'];reports.append(dict(name=n,full_type=full,full_type_sha256=sha,axioms=axioms));left=left[:m.start()]+left[m.end():]
 assert not left.strip()
 results[name]=dict(source=ident(src),reports=len(names),seconds=result['seconds'],peak_rss_bytes=result['peak_rss_bytes'],objects=result['objects'],plan_identity=module['plan_identity'],runner_identity=module['runner_identity'],report=module['full_type_axiom_report'],scope=module['scope'],source_closure_bound=len(seen))
 owned[name]=results[name]
assert len(results)==1
assert len(reports)==5

pending=out.with_name(out.name+'.pending');pending.mkdir()
for n in results:
 p=pending/'source/ShielddSecurity'/(n+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(sources[n])
evidence=dict(object_provenance_reviews=object_reviews,object_provenance_inputs=ident((root/'object-provenance-inputs.json').read_bytes()),resource_profile=profile,new_source_model_audits=5,status='passed',runtime_sha=manifest['runtime_sha'],scope=manifest['scope'],modules=results,complete_types_and_axioms=reports,reports=len(reports),dependency_sources_verified=len(sources),runtime_binding_review=ident((root/'runtime-binding-review.json').read_bytes()),manifest=ident((root/'successful-manifest.json').read_bytes()),refresh=ident(Path(__file__).read_bytes()),full_transfer='OPEN',native_credit=0,certification=False)
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,out);print(json.dumps(dict(status='passed',modules=len(results),reports=len(reports),dependency_sources_verified=len(sources))))
