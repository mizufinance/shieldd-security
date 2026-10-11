"""Fresh record proof layout repair with a direct reusable isEmpty_map term."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-installed-source-publication-20261011-01'
s=(old/'prepare_recipe.py').read_text()
a='nonempty := by\n    change ((inputs request.base.action).map (fun input => scalarKey (wordOf input))).isEmpty = false\n    rw [List.isEmpty_map]\n    exact request.sourceNonempty}'
b='nonempty := (List.isEmpty_map (l := inputs request.base.action) (f := fun input => scalarKey (wordOf input))).trans request.sourceNonempty}'
assert s.count(a)==1
s=s.replace(a,b)
s=s.replace('transfer-installed-source-publication-owned-floor-20261011-01','transfer-installed-source-publication-owned-floor-20261011-02')
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
p=ROOT/'prepare.py'; s=p.read_text()
a="[Path(__file__), ROOT / 'prepare_recipe.py', runner"
assert s.count(a)==1
s=s.replace(a,"[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner")
a="plan['artifact_policy']"; at=s.index(a)
pins="""failedInstalled = DIAG/'transfer-installed-source-publication-20261011-01'
plan['pins'] += [pin(failedInstalled/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferInstalledSourcePublication01.lean','project/ShielddSecurity/TransferInstalledSourcePublication01.lean','runs/01-TransferInstalledSourcePublication01/stdout.txt']]
"""
s=s[:at]+pins+s[at:]
p.write_text(s)
