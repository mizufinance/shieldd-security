"""Proof-only explicit radix64 type for the finite low-word rewrite."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-montgomery-value-20261011-02/recipe_source.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-montgomery-value-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-montgomery-value-owned-floor-20261011-03'")
a='  rw [Nat.add_mod, Nat.mod_mul_mod, Nat.mod_eq_of_lt word.toNat_lt, Nat.add_mod_mod]'
assert s.count(a)==1
s=s.replace(a,'  have wordBound : word.toNat < radix64 := word.toNat_lt\n  rw [Nat.add_mod, Nat.mod_mul_mod, Nat.mod_eq_of_lt wordBound, Nat.add_mod_mod]')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained02 = "failedMontgomery02 = DIAG/'transfer-scalar-montgomery-value-20261011-02'\\nplan['pins'] += [pin(failedMontgomery02/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarMontgomeryValue01.lean','project/ShielddSecurity/TransferScalarMontgomeryValue01.lean','runs/01-TransferScalarMontgomeryValue01/stdout.txt']]\\n"
s=s.replace('unique = {}',retained02+'unique = {}',1)
s=s.replace('Fresh02 proof-only nonlooping modular rewrites and explicit congrArg reduction, all thirteen contracts unchanged; failed01 warning/errors/full raw reports retained with zero credit.', 'Fresh03 proof-only explicit finite low-word bound in radix64 notation after fresh02 nonlooping modular rewrites and explicit congrArg reduction. All thirteen contracts unchanged; failed01/02 full raw errors/reports retained with zero credit.')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
