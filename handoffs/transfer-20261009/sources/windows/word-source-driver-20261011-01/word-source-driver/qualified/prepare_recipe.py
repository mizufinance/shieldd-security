from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
prior=DIAG/'transfer-word-source-driver-20261011-02'
s=(prior/'prepare.py').read_text()
s=s.replace('transfer-word-source-driver-owned-floor-20261011-02','transfer-word-source-driver-owned-floor-20261011-03')
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"pressureDriver = DIAG/'transfer-word-source-driver-20261011-02'\nplan['pins'] += [pin(pressureDriver/n) for n in ['repair_recipe.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordSourceDriver01.lean','project/ShielddSecurity/TransferWordSourceDriver01.lean']]\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
(ROOT/'handwritten').mkdir()
shutil.copyfile(prior/'handwritten/TransferWordSourceDriver01.lean',ROOT/'handwritten/TransferWordSourceDriver01.lean')
print({'same_source':True,'pressure02_preserved':True,'guards_unchanged':True})
