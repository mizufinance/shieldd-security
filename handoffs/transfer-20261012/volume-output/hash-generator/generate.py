from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
out=args.output.resolve();assert not out.exists();pending=out.with_name(out.name+'.pending');assert not pending.exists();pending.mkdir()
d=json.loads((root/'data.json').read_text());assert [c['index'] for c in d['calls']]==[149,150,151,152,153] and len(d['phases'])==325
sources=pending/'source-root/ShielddSecurity';sources.mkdir(parents=True)
for name in ['prefix','bindings','tail','composition','permutation','hash']:
 temp=pending/('generator-'+name)
 subprocess.run([sys.executable,'-B','-I','-S',str(root/(name+'.py')),str(temp)],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 for p in (temp/'source-root/ShielddSecurity').glob('*.lean'):
  target=sources/p.name;assert not target.exists();s=p.read_text().replace('\ndef ','\nnoncomputable def ');target.write_text('/- Generated from maintained volume output-hash generator; edit generator or templates. -/\n'+s)
 shutil.rmtree(temp)
(sources/'VolumeOutputHashes919.lean').write_text('import ShielddSecurity.VolumeOutputHashCapture913\n'+''.join('import ShielddSecurity.VolumeOutputHash918C'+str(ci)+'\n' for ci in [149,150,151,152,153])+'namespace ShielddSecurity.VolumeOutputHashes919\ndef callCount : Nat := 5\nend ShielddSecurity.VolumeOutputHashes919\nset_option pp.all true in\n#check @ShielddSecurity.VolumeOutputHashes919.callCount\n#print axioms ShielddSecurity.VolumeOutputHashes919.callCount\n')
inventory={p.stem:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',p.read_text(),re.M)) for p in sources.glob('*.lean')}
(pending/'generation.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n');os.replace(pending,out)
print(json.dumps(dict(modules=len(inventory),audits=sum(len(x['audits']) for x in inventory.values()))))
