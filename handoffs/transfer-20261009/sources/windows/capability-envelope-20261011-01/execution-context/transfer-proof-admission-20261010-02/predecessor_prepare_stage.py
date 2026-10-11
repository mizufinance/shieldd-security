"""Qualify the owned registry admission model for an envelope/row association join."""
import ast
import hashlib
import json
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
def pin(path):
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
original=Path('C:/src/shieldd-formal/circuits/ShielddSecurity/TransferProofAdmissionModel.lean')
text=original.read_text()
text=re.sub(r'set_option pp\.all true in\n#check [^\n]+\n#print axioms [^\n]+\n','',text)
assert '#check' not in text and '#print' not in text
names=re.findall(r'^(?:noncomputable )?(?:structure|theorem|lemma|def) ([A-Za-z0-9_]+)',text,re.M)
assert len(names)==21
audits='\n'.join('set_option pp.all true in\n#check @ShielddSecurity.TransferProofAdmissionModel.'+n+
                  '\n#print axioms ShielddSecurity.TransferProofAdmissionModel.'+n for n in names)
source=ROOT/'handwritten/TransferProofAdmissionModel.lean'
source.parent.mkdir(parents=True,exist_ok=True);assert not source.exists()
source.write_text(text+'\n'+audits+'\n',encoding='utf-8',newline='\n')
(ROOT/'source-review.json').write_text(json.dumps([{'module':'TransferProofAdmissionModel',
    'prior_handwritten':pin(original),'candidate':pin(source),
    'body_changes':'Complete21-explicit-public-declaration audit inventory only; all proof bodies and finite200000 heartbeats preserved.'}],indent=2)+'\n')
recipe=(DIAG/'transfer-capability-acceptance-20261010-01/prepare.py').read_text()
recipe=recipe.replace('TransferAcceptance','TransferProofAdmissionModel')
recipe=recipe.replace('transfer-sdk-raw-authorization-floor-20261010-01','transfer-capability-owned-floor-20261010-01')
recipe=recipe.replace("floor['objects'] == 432", "floor['objects'] == 434")
recipe=recipe.replace('assert len(names) == 28','assert len(names) == 21')
recipe=recipe.replace("['Init.Data.List.Perm']", "['ShielddSecurity.TransferAcceptance']")
start=recipe.index("plan['scope'] = ");end=recipe.index("plan['source_repairs']",start)
scope='Existing independently executable local-registry relation lookup, claim-context gates, individual verification and separately fresh-randomized batch verification inputs, followed by exact capability minting. Claim/envelope byte association, native source/codec/key/cryptographic semantics remain OPEN. Batch Bool success supplies no per-entry knowledge consequence. Qualifies the prerequisite for constructive slot-capability-envelope association; no runtime/control/full Transfer certification credit.'
recipe=recipe[:start]+"plan['scope'] = "+repr(scope)+'\n'+recipe[end:]
recipe=recipe.replace('Existing handwritten proof bodies and finite options preserved; complete28-declaration audit inventory only.','Existing registry admission proof bodies and finite options preserved; complete21-declaration audit inventory only.')
recipe=recipe.replace('TRANSACTION_ACCEPTANCE_INTERFACE_QUALIFICATION','OWNED_PROOF_ADMISSION_INTERFACE_QUALIFICATION')
ast.parse(recipe)
(ROOT/'prepare.py').write_text(recipe,encoding='utf-8',newline='\n')
print(json.dumps({'audits':len(names),'candidate':pin(source),'prior':pin(original),'guard_changes':False}))
