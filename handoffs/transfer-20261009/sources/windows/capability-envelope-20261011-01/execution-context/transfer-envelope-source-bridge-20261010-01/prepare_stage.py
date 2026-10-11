"""Qualify the existing exact retained-envelope decoder association."""
import ast
import hashlib
import json
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
def pin(path):
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
original=Path('C:/src/shieldd-formal/circuits/ShielddSecurity/TransferEnvelopeSourceBridge.lean')
text=original.read_text()
text=re.sub(r'set_option pp\.all true in\n#check [^\n]+\n#print axioms [^\n]+\n','',text)
assert '#check' not in text and '#print' not in text
names=re.findall(r'^(?:noncomputable )?(?:structure|theorem|lemma|def) ([A-Za-z0-9_]+)',text,re.M)
assert len(names)==7
source=ROOT/'handwritten/TransferEnvelopeSourceBridge.lean'
source.parent.mkdir(parents=True,exist_ok=True);assert not source.exists()
audits='\n'.join('set_option pp.all true in\n#check @ShielddSecurity.TransferEnvelopeSourceBridge.'+n+
                  '\n#print axioms ShielddSecurity.TransferEnvelopeSourceBridge.'+n for n in names)
source.write_text(text+'\n'+audits+'\n',encoding='utf-8',newline='\n')
(ROOT/'source-review.json').write_text(json.dumps([{'module':'TransferEnvelopeSourceBridge',
    'prior_handwritten':pin(original),'candidate':pin(source),
    'body_changes':'Complete7-explicit-public-declaration inventory only; proof bodies and finite200000 heartbeats preserved.'}],indent=2)+'\n')
recipe=(DIAG/'transfer-proof-admission-20261010-01/prepare.py').read_text()
recipe=recipe.replace('TransferProofAdmissionModel','TransferEnvelopeSourceBridge')
recipe=recipe.replace('transfer-capability-owned-floor-20261010-01','transfer-proof-admission-owned-floor-20261010-01')
recipe=recipe.replace("floor['objects'] == 434", "floor['objects'] == 436")
recipe=recipe.replace('assert len(names) == 21','assert len(names) == 7')
recipe=recipe.replace("'imports': ['ShielddSecurity.TransferAcceptance']", "'imports': ['ShielddSecurity.TransferProofAdmissionModel']")
start=recipe.index("plan['scope'] = ");end=recipe.index("plan['source_repairs']",start)
scope='Independent decodeEntries obtains each claim from the exact retained Item.envelope and preserves original item order. Successful local-registry individual/batch framing derives exact envelope/claim/statement/relation/registry association. Native Envelope parser/serializer, scalar/group decoding, setup and cryptographic verification contracts remain OPEN; no per-entry batch knowledge claim, runtime/control or full Transfer certification credit.'
recipe=recipe[:start]+"plan['scope'] = "+repr(scope)+'\n'+recipe[end:]
recipe=recipe.replace('Existing registry admission proof bodies and finite options preserved; complete21-declaration audit inventory only.','Existing retained-envelope association proof bodies and finite options preserved; complete7-declaration audit inventory only.')
recipe=recipe.replace('OWNED_PROOF_ADMISSION_INTERFACE_QUALIFICATION','RETAINED_ENVELOPE_INTERFACE_QUALIFICATION')
ast.parse(recipe)
(ROOT/'prepare.py').write_text(recipe,encoding='utf-8',newline='\n')
print(json.dumps({'audits':7,'candidate':pin(source),'prior':pin(original),'guard_changes':False}))
