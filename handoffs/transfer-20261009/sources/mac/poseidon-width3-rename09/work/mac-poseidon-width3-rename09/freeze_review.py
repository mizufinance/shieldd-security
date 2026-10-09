import hashlib,json,re,shutil
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-width3-rename09';P=S/'project';h=lambda b:hashlib.sha256(b).hexdigest();i=1
while(S/f'review-snapshot{i:02d}').exists():i+=1
D=S/f'review-snapshot{i:02d}';D.mkdir();roots=['TransferPoseidonWidth3ParentPage09Proof01','TransferPoseidonWidth3SecondTail09Controls01','TransferPoseidonWidth3Rename09Leaf01','TransferPoseidonWidth3Rename09ImportFloor01'];pending=[P/'ShielddSecurity'/f'{n}.lean' for n in roots];seen=set()
while pending:
 p=pending.pop()
 if p in seen:continue
 seen.add(p)
 for n in re.findall(r'^import (ShielddSecurity\.\S+)',p.read_text(),re.M):pending.append(P/(n.replace('.','/')+'.lean'))
files=[]
for p in sorted(seen):
 rel='project/'+str(p.relative_to(P));dest=D/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest);b=p.read_bytes();files.append(dict(path=rel,sha256=h(b),bytes=len(b)))
for p in sorted(S.glob('*.py'))+sorted(S.glob('*.lean.txt')):
 if p.name=='freeze_review.py':continue
 dest=D/'maintained'/p.name;dest.parent.mkdir(exist_ok=True);shutil.copyfile(p,dest);b=p.read_bytes();files.append(dict(path='maintained/'+p.name,sha256=h(b),bytes=len(b)))
p=D/'manifest.json';p.write_text(json.dumps(dict(scope='Source-only freeze, fresh kernel acceptance remains per receipt',root_modules=roots,files=files,descriptor=dict(path=str(O/'second-tail01.json'),sha256=h((O/'second-tail01.json').read_bytes()))),indent=2)+'\n');print(json.dumps(dict(path=str(p),sha256=h(p.read_bytes()),files=len(files),bytes=sum(x['bytes'] for x in files))))
