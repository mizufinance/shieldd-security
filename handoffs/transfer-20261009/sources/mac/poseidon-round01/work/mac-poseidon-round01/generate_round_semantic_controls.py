"""Instantiate maintained negative controls against the production checker."""
import hashlib,json,os,re
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-round01';P=S/'project/ShielddSecurity'
source=(S/'round-semantic-controls-template.lean.txt').read_text();records=[]
names=['ark_column_rejected','mds_mix_rejected','hint_column_rejected','row_column_rejected','port_binding_rejected','row_mutation_ran','column_rejection','ark_rejected','wrong_hint_rejected','coefficient_rejected','mix_rejection','port_rejection','mds_rejected','state_port_rejected']
for index in (1,4):
 tag=f'{index:02d}';ns=f'ShielddSecurity.TransferPoseidonRound{tag}SemanticControls01'
 s=source.replace('@ROUND@',tag).replace('@INDEX@',str(index)).replace('@ROWLIST@',','.join(f'row{i}' for i in range(1,25 if index==1 else 5)))
 cut=s.index('theorem column_rejection')
 data_ns=ns.replace('Controls01','ControlsData01')
 data=s[:cut].replace(ns,data_ns)+'end '+data_ns+'\n'
 header=s[:s.index('def alteredArk')].replace('import ShielddSecurity.TransferPoseidonRound'+tag+'SemanticProof01','import ShielddSecurity.TransferPoseidonRound'+tag+'SemanticControlsData01')
 wrapper=header+'open TransferPoseidonRound'+tag+'SemanticControlsData01\n'+s[cut:]
 for module_ns,text,subset in [(data_ns,data,names[:6]),(ns,wrapper,names[6:])]:
  for n in reversed(subset):
   start=re.search(r'^theorem '+re.escape(n)+r'\b',text,re.M).start()
   next_decl=re.search(r'^(theorem|end)\b',text[start+1:],re.M)
   at=start+1+next_decl.start()
   text=text[:at]+f'set_option pp.all true in\n#check @{module_ns}.{n}\n#print axioms {module_ns}.{n}\n\n'+text[at:]
  b=text.encode();p=P/(module_ns.split('.')[-1]+'.lean')
  if p.exists() and p.read_bytes()!=b:
   old=p.read_bytes();hist=O/'source-history';hist.mkdir(exist_ok=True);(hist/(p.stem+'-'+hashlib.sha256(old).hexdigest()+'.lean')).write_bytes(old)
  tmp=p.with_suffix('.tmp');tmp.write_bytes(b);os.replace(tmp,p);records.append(dict(module=p.stem,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
i=1
while (O/f'semantic-controls-generation{i:02d}.json').exists():i+=1
m=dict(generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),template_sha256=hashlib.sha256(source.encode()).hexdigest(),sources=records)
(O/f'semantic-controls-generation{i:02d}.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps(m))
