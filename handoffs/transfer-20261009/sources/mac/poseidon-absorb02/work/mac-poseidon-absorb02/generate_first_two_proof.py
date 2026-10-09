"""Atomic proof instance refresh from a maintained symbolic template."""
import hashlib,json,os,re
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-absorb02';P=S/'project/ShielddSecurity'
template=S/'first-two-proof-template.lean.txt';source=template.read_text();text=source;ns='ShielddSecurity.TransferPoseidonFirstTwo02Proof01'
names=re.findall(r'^theorem (\w+)',source,re.M)
for name in reversed(names):
 start=re.search(r'^theorem '+name+r'\b',text,re.M).start();next_decl=re.search(r'^(theorem|variable|def|end)\b',text[start+1:],re.M);at=start+1+next_decl.start()
 text=text[:at]+f'set_option pp.all true in\n#check @{ns}.{name}\n#print axioms {ns}.{name}\n\n'+text[at:]
b=text.encode();p=P/'TransferPoseidonFirstTwo02Proof01.lean';h=lambda b:hashlib.sha256(b).hexdigest()
if p.exists() and p.read_bytes()!=b:
 old=p.read_bytes();hist=O/'source-history';hist.mkdir(exist_ok=True);(hist/(p.stem+'-'+h(old)+'.lean')).write_bytes(old)
tmp=p.with_suffix('.tmp');tmp.write_bytes(b);os.replace(tmp,p)
i=1
while (O/f'first-two-proof-generation{i:02d}.json').exists():i+=1
m=dict(generator_sha256=h(Path(__file__).read_bytes()),template_sha256=h(source.encode()),sources=[dict(module=p.stem,sha256=h(b),bytes=len(b))],audit_names=names)
(O/f'first-two-proof-generation{i:02d}.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps(m))
