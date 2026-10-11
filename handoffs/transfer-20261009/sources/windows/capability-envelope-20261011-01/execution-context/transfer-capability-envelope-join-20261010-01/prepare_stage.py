"""Freeze a constructive verification-provenance/slot/retained-envelope join."""
import ast
import json
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
source=ROOT/'handwritten/TransferCapabilityEnvelope01.lean'
text=source.read_text();assert '#check' not in text
names=re.findall(r'^(?:noncomputable )?(?:structure|theorem|lemma|def) ([A-Za-z0-9_]+)',text,re.M)
assert len(names)==7
audits='\n'.join('set_option pp.all true in\n#check @ShielddSecurity.TransferCapabilityEnvelope01.'+n+
                  '\n#print axioms ShielddSecurity.TransferCapabilityEnvelope01.'+n for n in names)
source.write_text(text+'\n'+audits+'\n',encoding='utf-8',newline='\n')
recipe=(DIAG/'transfer-capability-rows-20261010-01/prepare.py').read_text()
recipe=recipe.replace('TransferCapabilityRows01','TransferCapabilityEnvelope01')
recipe=recipe.replace('transfer-capability-owned-floor-20261010-01','transfer-envelope-owned-floor-20261010-01')
recipe=recipe.replace("floor['objects'] == 434", "floor['objects'] == 437")
recipe=recipe.replace('assert len(names) == 15','assert len(names) == 7')
recipe=recipe.replace("['ShielddSecurity.TransferAcceptance','Init.Data.List.Sort']", "['ShielddSecurity.TransferCapabilityRows01','ShielddSecurity.TransferEnvelopeSourceBridge']")
start=recipe.index("plan['pins'] += [pin(Path(__file__))");end=recipe.index("plan['pins'] += floor",start)
recipe=recipe[:start]+"plan['pins'] += [pin(Path(__file__)), pin(ROOT / 'prepare_stage.py'), pin(source), pin(target), pin(runner), pin(POOL / 'composition-review.json'), pin(POOL / 'prepare.py'), pin(POOL / 'prepare_recipe.py')]\n"+recipe[end:]
start=recipe.index("plan['pins'] += [pin(ROOT / 'runtime-source'");end=recipe.index("plan['kind']",start)
recipe=recipe[:start]+recipe[end:]
start=recipe.index("plan['scope'] = ");end=recipe.index("plan['source_repairs']",start)
scope='Successful constructive slot validation and provenance from the independent individual/batch framing programs derive exact retained-envelope decoding, local registry relation selection, independent location family and singleton statement/one commitment claim binding at every expected slot. No BoundRows, desired item/coverage/claim equation or per-entry batch knowledge premise is supplied. Rust extraction/container/byte-decoder/key/cryptographic and full Transfer circuit/runtime/state/durability refinements remain OPEN; no runtime/control/full Transfer certification credit.'
recipe=recipe[:start]+"plan['scope'] = "+repr(scope)+'\n'+recipe[end:]
recipe=recipe.replace('CONSTRUCTIVE_CAPABILITY_ROW_JOIN','CONSTRUCTIVE_CAPABILITY_ENVELOPE_JOIN')
ast.parse(recipe)
(ROOT/'prepare.py').write_text(recipe,encoding='utf-8',newline='\n')
print(json.dumps({'audits':7,'scope':scope,'guard_changes':False}))
