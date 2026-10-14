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
reports=[];results={}
for module in manifest['modules']:
 name=module['module'];src=checked(root/module['source_path'],module['source']);assert src==sources[name]
 meta=packet/'original-metadata'/name;plan_bytes=checked(meta/'plan.json',module['plan_identity']);runner=checked(meta/'execute_bounded.py',module['runner_identity'])
 assert hashlib.sha256(runner).hexdigest()=='7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
 plan=json.loads(plan_bytes);target=next(t for t in plan['targets'] if t['module']==name);assert ident(src)=={k:target['source'][k] for k in ['bytes','sha256']}
 assert plan['limits']['threads']==1 and plan['limits']['heap_mib']==1536
 assert plan['pressure_limits']['one_host_one_heavy'] and plan['pressure_limits']['owned_job_memory_and_rss_bytes']==4*1024**3
 pinset={(r['bytes'],r['sha256']) for r in plan['pins']};seen=set()
 def visit(n):
  if n in seen:return
  seen.add(n);data=sources[n];assert (len(data),hashlib.sha256(data).hexdigest()) in pinset,n
  for child in re.findall(r'(?m)^import ShielddSecurity\.([A-Za-z0-9_]+)\s*$',data.decode()):visit(child)
 visit(name)
 events=[json.loads(line) for line in checked(packet/module['original_events']['path'],module['original_events']).decode().splitlines()]
 finishes=[e['result'] for e in events if e['event']=='attempt_finished'];assert len(finishes)==1;result=finishes[0];assert result['status']=='passed' and result['seconds']<240 and result['peak_rss_bytes']<4*1024**3
 assert '-j1' in result['command'] and '-M1536' in result['command']
 raw=checked(packet/module['full_type_axiom_report']['path'],module['full_type_axiom_report']);assert ident(raw)=={k:result['stdout'][k] for k in ['bytes','sha256']};left=raw.decode()
 assert not re.search(r'(?im)^.*(?:warning|error|panic):|sorryAx|uncaught exception|internal exception',left)
 names=re.findall(r'(?m)^#check @([\w.]+)\s*$',src.decode());assert names==re.findall(r'(?m)^#print axioms ([\w.]+)\s*$',src.decode());names=[n if n.startswith('ShielddSecurity.') else 'ShielddSecurity.'+name+'.'+n for n in names];assert names==target['audit_names'] and set(names)==set(result['audits'])
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|extern|native_decide|run_tac|initialize|ofReduceBool|skipKernelTC)\b',src.decode())
 for n in names:
  pattern=r'^@?'+re.escape(n)+r'(?:\.\{[^}\n]*\})?\s*:[\s\S]*?^\''+re.escape(n)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$";ms=list(re.finditer(pattern,left,re.M));assert len(ms)==1,n;m=ms[0];full=m.group(0).split("\n'"+n+"'",1)[0].strip();axioms=[] if m.group(1) is None else [x.strip() for x in m.group(1).split(',')];assert set(axioms)<= {'propext','Quot.sound','Classical.choice'};assert axioms==result['audits'][n]['axioms'];sha=hashlib.sha256(full.encode()).hexdigest();assert sha==result['audits'][n]['full_type_sha256'];reports.append(dict(name=n,full_type=full,full_type_sha256=sha,axioms=axioms));left=left[:m.start()]+left[m.end():]
 assert not left.strip()
 results[name]=dict(source=ident(src),reports=len(names),seconds=result['seconds'],peak_rss_bytes=result['peak_rss_bytes'],objects=result['objects'],plan_identity=module['plan_identity'],runner_identity=module['runner_identity'],report=module['full_type_axiom_report'],scope=module['scope'],source_closure_bound=len(seen))
assert len(results)==2
pending=out.with_name(out.name+'.pending');pending.mkdir()
for n in results:
 p=pending/'source/ShielddSecurity'/(n+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(sources[n])
evidence=dict(status='passed',runtime_sha=manifest['runtime_sha'],scope=manifest['scope'],modules=results,complete_types_and_axioms=reports,reports=len(reports),dependency_sources_verified=len(sources),manifest=ident((root/'successful-manifest.json').read_bytes()),refresh=ident(Path(__file__).read_bytes()),full_transfer='OPEN',native_credit=0,certification=False)
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,out);print(json.dumps(dict(status='passed',modules=len(results),reports=len(reports),dependency_sources_verified=len(sources))))
