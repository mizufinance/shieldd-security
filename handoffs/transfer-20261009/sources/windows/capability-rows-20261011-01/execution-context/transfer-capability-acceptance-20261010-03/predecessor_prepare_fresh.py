"""Remove one unused simp argument; keep the rejected qualification immutable."""
import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent/'transfer-capability-acceptance-20261010-01'
def pin(path):
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
source = PRIOR/'handwritten/TransferAcceptance.lean'
text = source.read_text()
old = '  simp only [Prod.fst] at same\n'
assert text.count(old) == 1
target = ROOT/'handwritten/TransferAcceptance.lean'
target.parent.mkdir(parents=True,exist_ok=True)
assert not target.exists()
target.write_text(text.replace(old,''),encoding='utf-8',newline='\n')
records=json.loads((PRIOR/'source-review.json').read_text())
records[0]['predecessor_candidate']=pin(source)
records[0]['candidate']=pin(target)
records[0]['body_changes']='Remove the one unused Prod.fst simp invocation; remaining proof bodies and finite options preserved. Rejected warning attempt has zero proof/control credit.'
(ROOT/'source-review.json').write_text(json.dumps(records,indent=2)+'\n')
(ROOT/'predecessor_prepare_stage.py').write_bytes((PRIOR/'prepare_stage.py').read_bytes())
recipe=(PRIOR/'prepare.py').read_text()
recipe=recipe.replace("pin(ROOT / 'prepare_stage.py')", "pin(ROOT / 'prepare_fresh.py'), pin(ROOT / 'predecessor_prepare_stage.py')")
recipe=recipe.replace("plan['kind'] =", "plan['pins'] += [pin(ROOT.parent / 'transfer-capability-acceptance-20261010-01' / name) for name in ['plan.json','events.jsonl','execute_bounded.py','prepare.py','source-review.json','handwritten/TransferAcceptance.lean','runs/01-TransferAcceptance/stdout.txt']]\nplan['kind'] =")
recipe=recipe.replace('Existing handwritten proof bodies and finite options preserved; complete28-declaration audit inventory only.',records[0]['body_changes'])
ast.parse(recipe)
(ROOT/'prepare.py').write_text(recipe,encoding='utf-8',newline='\n')
print(json.dumps({'candidate':pin(target),'rejected_plan':pin(PRIOR/'plan.json'),'audits':28,'guard_changes':False}))
