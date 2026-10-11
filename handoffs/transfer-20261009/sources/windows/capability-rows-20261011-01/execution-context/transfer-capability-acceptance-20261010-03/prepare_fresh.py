"""Use an explicit definitional equality before slot substitution."""
import ast
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PRIOR=ROOT.parent/'transfer-capability-acceptance-20261010-02'
def pin(path):
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
source=PRIOR/'handwritten/TransferAcceptance.lean'
text=source.read_text()
old='  obtain ⟨actualSlot, capability⟩ := row\n  subst actualSlot'
new='  obtain ⟨actualSlot, capability⟩ := row\n  change actualSlot = slot at same\n  subst actualSlot'
assert text.count(old)==1
target=ROOT/'handwritten/TransferAcceptance.lean'
target.parent.mkdir(parents=True,exist_ok=True)
assert not target.exists()
target.write_text(text.replace(old,new),encoding='utf-8',newline='\n')
records=json.loads((PRIOR/'source-review.json').read_text())
records[0]['second_predecessor_candidate']=pin(source)
records[0]['candidate']=pin(target)
records[0]['body_changes']='Explicit change actualSlot = slot exposes the pair projection before subst, replacing the rejected unused simp. Two predecessors remain immutable with zero proof/control credit; all finite options unchanged.'
(ROOT/'source-review.json').write_text(json.dumps(records,indent=2)+'\n')
for name in ['predecessor_prepare_stage.py','prepare_fresh.py']:
    (ROOT/('predecessor_'+name if name=='prepare_fresh.py' else name)).write_bytes((PRIOR/name).read_bytes())
recipe=(PRIOR/'prepare.py').read_text()
recipe=recipe.replace("pin(ROOT / 'prepare_fresh.py')", "pin(ROOT / 'prepare_fresh.py'), pin(ROOT / 'predecessor_prepare_fresh.py')")
recipe=recipe.replace("plan['kind'] =", "plan['pins'] += [pin(ROOT.parent / 'transfer-capability-acceptance-20261010-02' / name) for name in ['plan.json','events.jsonl','execute_bounded.py','prepare.py','source-review.json','handwritten/TransferAcceptance.lean','runs/01-TransferAcceptance/stdout.txt']]\nplan['kind'] =")
start=recipe.index("plan['source_repairs'] = ");end=recipe.index("(ROOT / 'plan.json')",start)
recipe=recipe[:start]+"plan['source_repairs'] = "+repr(records[0]['body_changes'])+'\n'+recipe[end:]
ast.parse(recipe)
(ROOT/'prepare.py').write_text(recipe,encoding='utf-8',newline='\n')
print(json.dumps({'candidate':pin(target),'rejected_plan':pin(PRIOR/'plan.json'),'audits':28,'guard_changes':False}))
