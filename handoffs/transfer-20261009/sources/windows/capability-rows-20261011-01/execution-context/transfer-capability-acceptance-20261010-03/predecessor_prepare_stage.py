"""Qualify the existing acceptance interfaces before a constructive slot join."""
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
source = Path('C:/src/shieldd-formal/circuits/ShielddSecurity/TransferAcceptance.lean')
def pin(path):
    return {'path': str(path), 'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
body = source.read_text()
body = re.sub(r'set_option pp\.all true in\n#check [^\n]+\n#print axioms [^\n]+\n', '', body)
assert '#check' not in body and '#print' not in body
names = re.findall(r'^(?:noncomputable )?(?:structure|theorem|lemma|def) ([A-Za-z0-9_]+)', body, re.M)
assert len(names) == 28
body += '\n' + '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.TransferAcceptance.'+n+
                           '\n#print axioms ShielddSecurity.TransferAcceptance.'+n for n in names) + '\n'
target = ROOT/'handwritten/TransferAcceptance.lean'
target.parent.mkdir(parents=True, exist_ok=True)
assert not target.exists()
target.write_text(body, encoding='utf-8', newline='\n')
(ROOT/'source-review.json').write_text(json.dumps([{'module':'TransferAcceptance',
    'prior_handwritten':pin(source),'candidate':pin(target),
    'body_changes':'Complete28-public-declaration audit inventory only; existing finite200000 heartbeats and proof bodies unchanged.'}],indent=2)+'\n')
recipe = (DIAG/'transfer-sdk-raw-authorization-join-20261010-01/prepare.py').read_text()
recipe = recipe.replace('SDKRawAuthorization01','TransferAcceptance')
recipe = recipe.replace('(?:theorem|lemma|def)', '(?:structure|theorem|lemma|def)')
recipe = recipe.replace('assert len(names) == 13','assert len(names) == 28')
recipe = recipe.replace("['ShielddSecurity.SDKNativeSpendAuth01', 'ShielddSecurity.ShielddNativeAuthorizationRaw', 'Mathlib.Data.List.OfFn']", "['Init.Data.List.Perm']")
start = recipe.index("plan['pins'] += [pin(Path(__file__))"); end = recipe.index("plan['pins'] += floor", start)
recipe = recipe[:start] + "plan['pins'] += [pin(Path(__file__)), pin(ROOT / 'prepare_stage.py'), pin(ROOT / 'source-review.json'), pin(Path('C:/src/shieldd-formal/circuits/ShielddSecurity/TransferAcceptance.lean')), pin(source), pin(target), pin(runner), pin(POOL / 'composition-review.json'), pin(POOL / 'prepare.py'), pin(POOL / 'prepare_recipe.py')]\n" + recipe[end:]
start = recipe.index("plan['scope'] = "); end = recipe.index("plan['source_repairs']", start)
scope = 'Qualification of existing transaction acceptance interfaces and symbolic slot/registry/item consequences. BoundRows remains an explicit premise here; constructive native capability-row validation is the next join. Rust BTreeMap/ProofSlot/byte-envelope/source correspondence and cryptographic verifier contracts remain OPEN. No runtime/control/full Transfer certification credit.'
recipe = recipe[:start] + "plan['scope'] = " + repr(scope) + '\n' + recipe[end:]
recipe = recipe.replace('New handwritten input-boundary proof; no generated edits or new axioms.', 'Existing handwritten proof bodies and finite options preserved; complete28-declaration audit inventory only.')
recipe = recipe.replace('MATHEMATICAL_SDK_CODEC_SUCCESSOR','TRANSACTION_ACCEPTANCE_INTERFACE_QUALIFICATION')
ast.parse(recipe)
(ROOT/'prepare.py').write_text(recipe, encoding='utf-8', newline='\n')
print(json.dumps({'module':'TransferAcceptance','audits':len(names),'candidate':pin(target),'prior':pin(source),'guard_changes':False}))
