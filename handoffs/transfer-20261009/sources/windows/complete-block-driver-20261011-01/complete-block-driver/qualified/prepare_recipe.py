"""Fresh case-split witness repair; retain both original contracts and failed raw output."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-complete-block-driver-20261011-01'
s=(old/'prepare_recipe.py').read_text()
a='refine ⟨final, ran, same.symm, ?_⟩';b='refine ⟨final, rfl, same.symm, ?_⟩';assert s.count(a)==1
s=s.replace(a,b).replace('transfer-complete-block-driver-owned-floor-20261011-01','transfer-complete-block-driver-owned-floor-20261011-02')
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
p=ROOT/'prepare.py';s=p.read_text();a="[Path(__file__), ROOT / 'prepare_recipe.py', runner";assert s.count(a)==1
s=s.replace(a,"[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner")
a="plan['artifact_policy']";at=s.index(a)
pins="""failedDriver=DIAG/'transfer-complete-block-driver-20261011-01'
plan['pins'] += [pin(failedDriver/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCompleteBlockDriver01.lean','project/ShielddSecurity/TransferCompleteBlockDriver01.lean','runs/01-TransferCompleteBlockDriver01/stdout.txt']]
"""
s=s[:at]+pins+s[at:];p.write_text(s)
