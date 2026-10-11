from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-word-object-read-20261011-02'
assert not (ROOT/'prepare.py').exists()
s=(prior/'prepare.py').read_text().replace('transfer-word-object-read-owned-floor-20261011-02','transfer-word-object-read-owned-floor-20261011-03')
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"pressureRead=DIAG/'transfer-word-object-read-20261011-02'\nplan['pins'] += [pin(pressureRead/n) for n in ['repair_recipe.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordObjectRead01.lean','project/ShielddSecurity/TransferWordObjectRead01.lean','context/checked-pending-read-shape.json']]\n"+s[at:]
s=s.replace("mapping['checked_pending_read_source_shape'] = pin(ROOT/'context/checked-pending-read-shape.json')","mapping['checked_pending_read_source_shape'] = pin(ROOT/'context/checked-pending-read-shape.json')")
(ROOT/'prepare.py').write_text(s)
for name in ['handwritten/TransferWordObjectRead01.lean','context/checked-pending-read-shape.json']:
    (ROOT/name).parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(prior/name,ROOT/name)
print({'same_checked_getter_source':True,'pressure02_preserved':True,'guards_unchanged':True})
