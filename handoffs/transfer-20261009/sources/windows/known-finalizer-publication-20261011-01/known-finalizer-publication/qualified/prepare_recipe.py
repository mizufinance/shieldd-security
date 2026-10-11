"""Fresh source layout repair; retain setup01 and complete failed02 raw evidence."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-known-finalizer-publication-20261011-02'
s=(old/'recipe_source.py').read_text()
a='verifiable := mergeWrites delta.cache.verifiable effects.verifiable,\n    nonverifiable'
assert s.count(a)==1
s=s.replace(a,'verifiable := mergeWrites delta.cache.verifiable effects.verifiable, nonverifiable')
s=s.replace('transfer-known-finalizer-publication-owned-floor-20261011-02','transfer-known-finalizer-publication-owned-floor-20261011-03')
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
p=ROOT/'prepare.py'; s=p.read_text()
a="[Path(__file__), ROOT / 'prepare_recipe.py', runner"
assert s.count(a)==1
s=s.replace(a,"[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner")
a="plan['artifact_policy']"; at=s.index(a)
pins="""plan['pins'] += [pin(DIAG/'transfer-known-finalizer-publication-20261011-01/prepare_recipe.py'),pin(DIAG/'transfer-known-finalizer-publication-20261011-01/handwritten/TransferKnownFinalizerPublication01.lean')]
failedFinalizer = DIAG/'transfer-known-finalizer-publication-20261011-02'
plan['pins'] += [pin(failedFinalizer/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferKnownFinalizerPublication01.lean','project/ShielddSecurity/TransferKnownFinalizerPublication01.lean','runs/01-TransferKnownFinalizerPublication01/stdout.txt']]
"""
s=s[:at]+pins+s[at:]
p.write_text(s)
