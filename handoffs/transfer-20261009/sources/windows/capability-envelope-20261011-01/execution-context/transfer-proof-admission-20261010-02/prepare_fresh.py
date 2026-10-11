"""Rename a constructor-like local binder; preserve the rejected warning attempt."""
import ast
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PRIOR=ROOT.parent/'transfer-proof-admission-20261010-01'
def pin(path):
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
source=PRIOR/'handwritten/TransferProofAdmissionModel.lean'
text=source.read_text()
old='      | some unit =>\n          cases unit'
new='      | some checkedUnit =>\n          cases checkedUnit'
assert text.count(old)==1
target=ROOT/'handwritten/TransferProofAdmissionModel.lean'
target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists()
target.write_text(text.replace(old,new),encoding='utf-8',newline='\n')
records=json.loads((PRIOR/'source-review.json').read_text())
records[0]['predecessor_candidate']=pin(source)
records[0]['candidate']=pin(target)
records[0]['body_changes']='Rename local unit binder to checkedUnit to clear constructor-name lint. Proof statements and branches, finite options and physical guards unchanged; rejected predecessor gets zero proof/control credit.'
(ROOT/'source-review.json').write_text(json.dumps(records,indent=2)+'\n')
(ROOT/'predecessor_prepare_stage.py').write_bytes((PRIOR/'prepare_stage.py').read_bytes())
recipe=(PRIOR/'prepare.py').read_text()
recipe=recipe.replace("pin(ROOT / 'prepare_stage.py')", "pin(ROOT / 'prepare_fresh.py'), pin(ROOT / 'predecessor_prepare_stage.py')")
recipe=recipe.replace("plan['kind'] =", "plan['pins'] += [pin(ROOT.parent / 'transfer-proof-admission-20261010-01' / name) for name in ['plan.json','events.jsonl','execute_bounded.py','prepare.py','source-review.json','handwritten/TransferProofAdmissionModel.lean','runs/01-TransferProofAdmissionModel/stdout.txt']]\nplan['kind'] =")
start=recipe.index("plan['source_repairs'] = ");end=recipe.index("(ROOT / 'plan.json')",start)
recipe=recipe[:start]+"plan['source_repairs'] = "+repr(records[0]['body_changes'])+'\n'+recipe[end:]
ast.parse(recipe)
(ROOT/'prepare.py').write_text(recipe,encoding='utf-8',newline='\n')
print(json.dumps({'candidate':pin(target),'rejected_plan':pin(PRIOR/'plan.json'),'audits':21,'guard_changes':False}))
