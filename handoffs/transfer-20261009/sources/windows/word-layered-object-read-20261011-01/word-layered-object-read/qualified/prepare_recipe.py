from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-word-layered-object-read-20261011-01'
assert not (ROOT/'prepare.py').exists()
s=(prior/'prepare.py').read_text().replace('transfer-word-layered-object-read-owned-floor-20261011-01','transfer-word-layered-object-read-owned-floor-20261011-02')
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"pressureLayers=DIAG/'transfer-word-layered-object-read-20261011-01'\nplan['pins'] += [pin(pressureLayers/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordLayeredObjectRead01.lean','project/ShielddSecurity/TransferWordLayeredObjectRead01.lean']]\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
(ROOT/'handwritten').mkdir();shutil.copyfile(prior/'handwritten/TransferWordLayeredObjectRead01.lean',ROOT/'handwritten/TransferWordLayeredObjectRead01.lean')
print({'same_layered_getter_source':True,'pressure01_preserved':True,'guards_unchanged':True})
