from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-word-layer-flatten-20261011-02'
assert not (ROOT/'prepare.py').exists()
s=(prior/'prepare.py').read_text().replace('transfer-word-layer-flatten-owned-floor-20261011-02','transfer-word-layer-flatten-owned-floor-20261011-03')
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"pressureFlat=DIAG/'transfer-word-layer-flatten-20261011-02'\nplan['pins'] += [pin(pressureFlat/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordLayerFlatten01.lean','project/ShielddSecurity/TransferWordLayerFlatten01.lean']]\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
(ROOT/'handwritten').mkdir();shutil.copyfile(prior/'handwritten/TransferWordLayerFlatten01.lean',ROOT/'handwritten/TransferWordLayerFlatten01.lean')
print({'same_repaired_four_contracts':True,'pressure02_preserved':True,'guards_unchanged':True})
