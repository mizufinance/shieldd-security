"""Fresh core-only congruence repair; all six contracts and guards retained."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-injective-key-publication-20261011-01'
s=(old/'prepare_recipe.py').read_text()
a='exact congrArg₂ List.cons pair.1 (@ih rest pair.2)'
b='exact (congrArg (fun h : Nat => h :: tail) pair.1).trans (congrArg (List.cons other) (@ih rest pair.2))'
assert s.count(a)==1
s=s.replace(a,b)
s=s.replace('transfer-injective-key-publication-owned-floor-20261011-01','transfer-injective-key-publication-owned-floor-20261011-02')
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
p=ROOT/'prepare.py'; s=p.read_text()
a="[Path(__file__), ROOT / 'prepare_recipe.py', runner"
assert s.count(a)==1
s=s.replace(a,"[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner")
a="plan['artifact_policy']"; at=s.index(a)
pins="""failedKeyCode = DIAG/'transfer-injective-key-publication-20261011-01'
plan['pins'] += [pin(failedKeyCode/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferInjectiveKeyPublication01.lean','project/ShielddSecurity/TransferInjectiveKeyPublication01.lean','runs/01-TransferInjectiveKeyPublication01/stdout.txt']]
"""
s=s[:at]+pins+s[at:]
p.write_text(s)
