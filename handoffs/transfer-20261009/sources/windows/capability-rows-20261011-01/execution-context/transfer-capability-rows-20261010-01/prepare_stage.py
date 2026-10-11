"""Freeze a symbolic capability-row constructor and exact runtime review context."""
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
def pin(path):
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
source=ROOT/'handwritten/TransferCapabilityRows01.lean'
text=source.read_text();assert '#check' not in text
names=re.findall(r'^(?:noncomputable )?(?:structure|theorem|lemma|def) ([A-Za-z0-9_]+)',text,re.M)
assert len(names)==15
audits='\n'.join('set_option pp.all true in\n#check @ShielddSecurity.TransferCapabilityRows01.'+n+
                  '\n#print axioms ShielddSecurity.TransferCapabilityRows01.'+n for n in names)
source.write_text(text+'\n'+audits+'\n',encoding='utf-8',newline='\n')
runtime=Path('C:/src/shieldd-pr160-844389ee')
assert subprocess.check_output(['git','-C',str(runtime),'rev-parse','HEAD']).decode().strip()=='844389ee069e1fb2e576708842d0b389b4d9a44a'
assert not subprocess.check_output(['git','-C',str(runtime),'status','--porcelain'])
records=[]
for relative,role in [
    ('crates/core/app/src/stateless_cache.rs','Owned slot-map insertion, coverage and per-capability checks'),
    ('crates/crypto/proof-params/src/pari.rs','Exact verified item and registry identity API'),
    ('crates/core/app/src/app/delivery.rs','Current active registry check at delivery'),
    ('crates/core/component/shielded-pool/src/component/action_handler/transfer.rs','Transfer family and exact proof item check before execution')]:
    original=runtime/relative;copy=ROOT/'runtime-source'/relative
    copy.parent.mkdir(parents=True,exist_ok=True);assert not copy.exists()
    copy.write_bytes(original.read_bytes());assert pin(copy)['sha256']==pin(original)['sha256']
    records.append({'runtime_relative_path':relative,'role':role,'original':pin(original),'copy':pin(copy)})
(ROOT/'runtime-source-identities.json').write_text(json.dumps({'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
    'files':records,'scope':'Identity and review context only; native finite-map/order/extraction/byte equality and cryptographic contracts remain OPEN.',
    'runtime_test_credit':0,'semantic_correspondence_credit':0,'certification':False},indent=2)+'\n')
recipe=(DIAG/'transfer-capability-acceptance-20261010-01/prepare.py').read_text()
recipe=recipe.replace('TransferAcceptance','TransferCapabilityRows01')
recipe=recipe.replace('transfer-sdk-raw-authorization-floor-20261010-01','transfer-capability-owned-floor-20261010-01')
recipe=recipe.replace("floor['objects'] == 432", "floor['objects'] == 434")
recipe=recipe.replace('assert len(names) == 28','assert len(names) == 15')
recipe=recipe.replace("['Init.Data.List.Perm']", "['ShielddSecurity.TransferAcceptance','Init.Data.List.Sort']")
start=recipe.index("plan['pins'] += [pin(Path(__file__))");end=recipe.index("plan['pins'] += floor",start)
recipe=recipe[:start]+"plan['pins'] += [pin(Path(__file__)), pin(ROOT / 'prepare_stage.py'), pin(ROOT / 'prepare_family_check.py'), pin(ROOT / 'predecessor_no_family_source.lean.txt'), pin(ROOT / 'runtime-source-identities.json'), pin(source), pin(target), pin(runner), pin(POOL / 'composition-review.json'), pin(POOL / 'prepare.py'), pin(POOL / 'prepare_recipe.py')]\n"+recipe[end:]
recipe=recipe.replace("plan['kind'] =", "plan['pins'] += [pin(ROOT / 'runtime-source' / r['runtime_relative_path']) for r in json.loads((ROOT / 'runtime-source-identities.json').read_text())['files']]\nplan['kind'] =")
start=recipe.index("plan['scope'] = ");end=recipe.index("plan['source_repairs']",start)
scope='Executable slot-map insertion rejects duplicates, sorted-key comparison derives exact coverage, and per-row registry, independent ProofLocation family and exact Item checks derive BoundRows for both returned map and original inputs. No BoundRows/target coverage equation is assumed. Rust finite-map/ProofSlot ordering/extracted-location/primitive byte-envelope identity and cryptographic verifier contracts remain OPEN; no runtime/control/full Transfer certification credit.'
recipe=recipe[:start]+"plan['scope'] = "+repr(scope)+'\n'+recipe[end:]
recipe=recipe.replace('Existing handwritten proof bodies and finite options preserved; complete28-declaration audit inventory only.','New handwritten symbolic source-program join; no generated source/evidence edits, new axioms or physical guard changes.')
recipe=recipe.replace('TRANSACTION_ACCEPTANCE_INTERFACE_QUALIFICATION','CONSTRUCTIVE_CAPABILITY_ROW_JOIN')
ast.parse(recipe)
(ROOT/'prepare.py').write_text(recipe,encoding='utf-8',newline='\n')
print(json.dumps({'audits':15,'candidate':pin(source),'runtime_files':len(records),'guard_changes':False}))
