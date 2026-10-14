from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
out=args.output.resolve();assert not out.exists();pending=out.with_name(out.name+'.pending');assert not pending.exists();pending.mkdir()
d=json.loads((root/'data.json').read_text());assert len(d['calls'])==1 and d['calls'][0]['index']==123 and d['calls'][0]['call']['domain']==4 and d['calls'][0]['call']['inputs']==[[1,1501],[1,1502],[1,1509],[1,1510],[1,3]] and len(d['phases'])==65
sources=pending/'source-root/ShielddSecurity';sources.mkdir(parents=True)
for name in ['prefix','bindings','tail','permutation']:
 temp=pending/('generator-'+name)
 subprocess.run([sys.executable,'-B','-I','-S',str(root/(name+'.py')),str(temp)],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 for p in (temp/'source-root/ShielddSecurity').glob('*.lean'):
  target=sources/p.name;assert not target.exists();s=p.read_text().replace('\ndef ','\nnoncomputable def ');target.write_text('/- Generated from maintained volume subject-hash generator; edit generator or templates. -/\n'+s)
 shutil.rmtree(temp)
for name,template in [('VolumeSubjectHashComposition896','composition.lean.in'),('VolumeSubjectHash898','hash.lean.in')]:
 s=(root/template).read_text().replace('\ndef ','\nnoncomputable def ')
 (sources/(name+'.lean')).write_text('/- Generated from maintained volume subject-hash template. -/\n'+s)
inventory={p.stem:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',p.read_text(),re.M)) for p in sources.glob('*.lean')}
(pending/'generation.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n');os.replace(pending,out)
print(json.dumps(dict(modules=len(inventory),audits=sum(len(x['audits']) for x in inventory.values()))))
