"""Instantiate handwritten finite proofs; no observed truth is inserted."""
import hashlib,json,os
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-round01';P=S/'project/ShielddSecurity'
source=(S/'round-proof-template.lean.txt').read_text();records=[]
names=['coverage_checked','all_index_coverage','node_certificates','actual_copy_checked','rows_coverage_checked','emitted_identity','reverse_coverage','ordered_check','ordered','writes_check','writes_lower_bound','cut_support_checked','input_terms_outside','actual_copy_link','arbitrary_assignment_sound','legal','completed_rows','original_columns_preserved','original_inputs_preserved','completed_one','completed_copy','completed_cut_inputs','completed_values','total_round_assignment']
for round,nodes,last in [(1,150,24),(4,135,4)]:
 tag=f'{round:02d}';ns=f'ShielddSecurity.TransferPoseidonRound{tag}Proof01';s=source.replace('@ROUND@',tag).replace('@NODES@',str(nodes)).replace('@COPYROW@',str(last))
 for n in names:s+=f'\nset_option pp.all true in\n#check @{ns}.{n}\n#print axioms {ns}.{n}\n'
 b=s.encode();p=P/(f'TransferPoseidonRound{tag}Proof01.lean')
 if p.exists() and p.read_bytes()!=b:
  old=p.read_bytes();hist=O/'source-history';hist.mkdir(exist_ok=True);(hist/(p.stem+'-'+hashlib.sha256(old).hexdigest()+'.lean')).write_bytes(old)
 tmp=p.with_suffix('.tmp');tmp.write_bytes(b);os.replace(tmp,p);records.append(dict(module=p.stem,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
i=1
while (O/f'proof-generation{i:02d}.json').exists():i+=1
m=dict(generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),template_sha256=hashlib.sha256(source.encode()).hexdigest(),sources=records)
(O/f'proof-generation{i:02d}.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps(m))
