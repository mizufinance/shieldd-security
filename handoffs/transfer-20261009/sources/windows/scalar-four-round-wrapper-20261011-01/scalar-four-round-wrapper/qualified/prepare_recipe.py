"""Close two rewritten reflexive inequalities; all fourteen declarations unchanged."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-four-round-wrapper-20261011-01/prepare_recipe.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-four-round-wrapper-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-four-round-wrapper-owned-floor-20261011-02'")
a=':= by rw [four, modulus_words_have_four_limbs]'
assert s.count(a)==2
s=s.replace(a,':= by\n    rw [four, modulus_words_have_four_limbs]\n    exact Nat.le_refl 4')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained = "failedWrapper = DIAG/'transfer-scalar-four-round-wrapper-20261011-01'\\nplan['pins'] += [pin(failedWrapper/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/source-association.json','handwritten/TransferScalarFourRoundWrapper01.lean','project/ShielddSecurity/TransferScalarFourRoundWrapper01.lean','runs/01-TransferScalarFourRoundWrapper01/stdout.txt']]\\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh source-constant four-round finite carry wrapper range', 'Fresh02 proof-only closure of two rewritten reflexive inequalities; all fourteen declaration contracts unchanged, failed01 full raw diagnostics retained with zero credit. Fresh source-constant four-round finite carry wrapper range')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
