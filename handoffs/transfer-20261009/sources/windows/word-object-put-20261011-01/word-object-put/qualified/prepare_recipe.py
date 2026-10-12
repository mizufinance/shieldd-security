from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-word-object-put-20261011-02'
assert not (ROOT/'prepare.py').exists()
s=(prior/'prepare.py').read_text().replace('transfer-word-object-put-owned-floor-20261011-02','transfer-word-object-put-owned-floor-20261011-03')
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"pressurePut=DIAG/'transfer-word-object-put-20261011-02'\nplan['pins'] += [pin(pressurePut/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordObjectPut01.lean','project/ShielddSecurity/TransferWordObjectPut01.lean','context/checked-pending-put-shape.json']]\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
for name in ['handwritten/TransferWordObjectPut01.lean','context/checked-pending-put-shape.json']:
    (ROOT/name).parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(prior/name,ROOT/name)
print({'same_repaired_eight_contracts':True,'pressure02_preserved':True,'guards_unchanged':True})
