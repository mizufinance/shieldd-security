"""Proof-only repair of distributivity rewrite; original failed attempt retained."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-serialization-range-20261011-01/prepare_recipe.py').read_text()
a='simp only [Nat.add_mul, Nat.mul_comm]'
assert s.count(a)==1
s=s.replace(a,'rw [Nat.add_mul, Nat.mul_comm radix modulus]')
s=s.replace("POOL = DIAG / 'transfer-scalar-serialization-range-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-serialization-range-owned-floor-20261011-02'")
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
failedPins = "failed_scalar = DIAG / 'transfer-scalar-serialization-range-20261011-01'\\nplan['pins'] += [pin(failed_scalar/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarSerializationRange01.lean','project/ShielddSecurity/TransferScalarSerializationRange01.lean','runs/01-TransferScalarSerializationRange01/stdout.txt']]\\n"
s=s.replace('unique = {}', failedPins + 'unique = {}', 1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner", 1)
s=s.replace('Fresh symbolic scalar serialization range obligation', 'Proof-only distributivity repair of scalar range01; all eight declaration statements unchanged; failed01 complete raw diagnostics retained with zero credit. Fresh symbolic scalar serialization range obligation')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
