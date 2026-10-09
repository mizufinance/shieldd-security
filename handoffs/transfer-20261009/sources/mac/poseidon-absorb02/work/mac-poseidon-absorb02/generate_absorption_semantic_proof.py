"""Atomic instantiation of maintained proofs; no proof outcomes are inserted."""
import hashlib,json,os,re
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-absorb02';P=S/'project/ShielddSecurity'
source=(S/'absorption-semantic-proof-template.lean.txt').read_text();records=[]
names=['column_cases','round_checked','production_checked','absorption_binding','ordered_inputs_exact','iv_exact','before_values','output_binding','round_certificate','ports_exact','arbitrary_round_sound','arbitrary_graph_round','completed_round','total_native_round']
for index,last in [(0,16)]:
 tag=f'{index:02d}';ns='ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01'
 s=source.replace('@ROUND@',tag).replace('@INDEX@',str(index)).replace('@COPYROW@',str(last))
 for n in reversed(names):
  start=re.search(r'^theorem '+re.escape(n)+r'\b',s,re.M).start()
  next_decl=re.search(r'^(theorem|variable|end)\b',s[start+1:],re.M)
  at=start+1+next_decl.start()
  s=s[:at]+f'set_option pp.all true in\n#check @{ns}.{n}\n#print axioms {ns}.{n}\n\n'+s[at:]
 b=s.encode();p=P/'TransferPoseidonAbsorb02SemanticProof01.lean'
 if p.exists() and p.read_bytes()!=b:
  old=p.read_bytes();hist=O/'source-history';hist.mkdir(exist_ok=True);(hist/(p.stem+'-'+hashlib.sha256(old).hexdigest()+'.lean')).write_bytes(old)
 tmp=p.with_suffix('.tmp');tmp.write_bytes(b);os.replace(tmp,p);records.append(dict(module=p.stem,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
i=1
while (O/f'semantic-proof-generation{i:02d}.json').exists():i+=1
m=dict(generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),template_sha256=hashlib.sha256(source.encode()).hexdigest(),sources=records)
(O/f'semantic-proof-generation{i:02d}.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps(m))
