from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-word-layer-flatten-20261011-01'
assert not (ROOT/'prepare.py').exists()
s=(prior/'prepare.py').read_text().replace('transfer-word-layer-flatten-owned-floor-20261011-01','transfer-word-layer-flatten-owned-floor-20261011-02')
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"failedFlat=DIAG/'transfer-word-layer-flatten-20261011-01'\nplan['pins'] += [pin(failedFlat/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordLayerFlatten01.lean','project/ShielddSecurity/TransferWordLayerFlatten01.lean','runs/01-TransferWordLayerFlatten01/stdout.txt']]\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
source=(prior/'handwritten/TransferWordLayerFlatten01.lean').read_text()
a='''    change selectedLiveLayers ((rest.map (fun item => item.objects)).reverse)
      (applyCache parent layer).objects key = (applyLayers (applyCache parent layer) rest).objects key
    exact ih (applyCache parent layer)'''
b='''    have singleton : (fun k => selectedLiveLayers [layer.objects] parent.objects k) = (applyCache parent layer).objects := by
      funext k
      cases selected : layer.objects k <;> simp only [selectedLiveLayers, applyCache, overlay, selected]
    rw [singleton]
    exact ih (applyCache parent layer)'''
assert source.count(a)==1;source=source.replace(a,b)
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferWordLayerFlatten01.lean').write_text(source)
print({'proof_only_singleton_overlay_repair':True,'same_four_contracts':True,'failed01_zero_credit':True,'guards_unchanged':True})
