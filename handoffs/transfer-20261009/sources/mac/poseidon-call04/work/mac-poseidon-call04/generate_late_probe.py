"""Reproduce the bounded late partial MDS consumer measurement."""
import hashlib,json
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-call04';m='TransferPoseidonCall04LateMixProbe01';ns='ShielddSecurity.'+m
ls=['-- Generated bounded late-partial consumer measurement; no whole-call claim.','import ShielddSecurity.TransferPoseidonCall04Data07','set_option maxHeartbeats 900000','set_option maxRecDepth 8192','namespace '+ns,'open Compiler Poseidon ShielddSecurity.TransferPoseidonCall04Shared01 ShielddSecurity.TransferPoseidonCall04R60']
for i in range(6):ls.extend([f'theorem partial_mix{i} : canonical p (after ⟨{i},by decide⟩)=canonical p (mixLinear parameters.mds transformed ⟨{i},by decide⟩) := by decide +kernel','set_option pp.all true in',f'#check @{ns}.partial_mix{i}',f'#print axioms {ns}.partial_mix{i}'])
ls+=['end '+ns];b=('\n'.join(ls)+'\n').encode();p=S/'project/ShielddSecurity'/ (m+'.lean')
if p.exists():assert p.read_bytes()==b
else:p.write_bytes(b)
i=1
while (O/f'partial-probe-generation{i:02d}.json').exists():i+=1
(O/f'partial-probe-generation{i:02d}.json').write_text(json.dumps(dict(generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),module=m,sha256=hashlib.sha256(b).hexdigest(),round=60,maximum_precanonical_MDS_terms=316,scope='bounded six actual partial-round mix checks; no full65 credit'),indent=2)+'\n')
