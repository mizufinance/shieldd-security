from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-word-stage-cache-publication-20261011-02'
assert not (ROOT/'prepare.py').exists()
s=(OLD/'prepare.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-word-stage-cache-publication-owned-floor-20261011-02'","POOL = DIAG / 'transfer-word-stage-cache-publication-owned-floor-20261011-03'")
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"pressureCache=DIAG/'transfer-word-stage-cache-publication-20261011-02'\nplan['pins'] += [pin(pressureCache/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageCachePublication01.lean','project/ShielddSecurity/TransferWordStageCachePublication01.lean','runs/01-TransferWordStageCachePublication01/stdout.txt']]\n"+s[at:]
source=(OLD/'handwritten/TransferWordStageCachePublication01.lean').read_text()
assert source.count('⟨object, staged, exactCache.symm⟩')==1
source=source.replace('⟨object, staged, exactCache.symm⟩','⟨object, rfl, exactCache.symm⟩')
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferWordStageCachePublication01.lean').write_text(source)
(ROOT/'prepare.py').write_text(s)
print({'original_pressure_attempt_retained':True,'rewritten_witness_reflexivity':True,'guards_unchanged':True})
