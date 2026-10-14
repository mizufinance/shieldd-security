import gzip
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
out=args.output.resolve();assert not out.exists();pending=out.with_name(out.name+'.pending');assert not pending.exists();pending.mkdir()
d=json.loads(gzip.decompress((root/'data.json.gz').read_bytes()));assert [c['index'] for c in d['calls']]==list(range(125,149)) and len(d['phases'])==1560
sources=pending/'source-root/ShielddSecurity';sources.mkdir(parents=True)
for name in ['prefix','bindings','tail','composition','permutation','hash']:
 temp=pending/('generator-'+name)
 subprocess.run([sys.executable,'-B','-I','-S',str(root/(name+'.py')),str(temp)],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 for p in (temp/'source-root/ShielddSecurity').glob('*.lean'):
  target=sources/p.name;assert not target.exists();s=p.read_text().replace('\ndef ','\nnoncomputable def ');target.write_text('/- Generated from maintained volume path-hash generator; edit generator or templates. -/\n'+s)
 shutil.rmtree(temp)
(sources/'VolumePathHashes932.lean').write_text('import ShielddSecurity.VolumePathHashCapture926\n'+''.join('import ShielddSecurity.VolumePathHash931C'+str(ci)+'\n' for ci in list(range(125,149)))+'namespace ShielddSecurity.VolumePathHashes932\ndef callCount : Nat := 24\nend ShielddSecurity.VolumePathHashes932\nset_option pp.all true in\n#check @ShielddSecurity.VolumePathHashes932.callCount\n#print axioms ShielddSecurity.VolumePathHashes932.callCount\n')
# Group early blocks only; retain individually bounded late-round sources.
for ci in range(125,149):
 for first in (0,7):
  members=[sources/f'VolumePathHashTail928C{ci}B{j:02d}.lean' for j in range(first,first+7)]
  imports=[];bodies=[]
  for member in members:
   lines=member.read_text().splitlines()
   for line in lines:
    if line.startswith('import ') and line not in imports:imports.append(line)
   bodies.append('\n'.join(line for line in lines if not line.startswith('import ')))
  joined='\n'.join(imports)+'\n'+'\n'.join(bodies)+'\n';assert len(joined.encode())<=262144
  members[0].write_text(joined)
  for member in members[1:]:member.unlink()
 composition=sources/f'VolumePathHashComposition929C{ci}.lean';text=composition.read_text()
 for j in range(21):
  if j in (0,7) or j>=14:continue
  line=f'import ShielddSecurity.VolumePathHashTail928C{ci}B{j:02d}\n';assert text.count(line)==1;text=text.replace(line,'')
 composition.write_text(text)
inventory={p.stem:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',p.read_text(),re.M)) for p in sources.glob('*.lean')}
(pending/'generation.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n');os.replace(pending,out)
print(json.dumps(dict(modules=len(inventory),audits=sum(len(x['audits']) for x in inventory.values()))))
