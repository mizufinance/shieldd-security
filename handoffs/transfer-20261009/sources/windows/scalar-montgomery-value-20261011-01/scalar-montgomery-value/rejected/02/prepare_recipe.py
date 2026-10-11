"""Proof-only nonlooping modular rewrites and explicit congrArg reduction."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-montgomery-value-20261011-01/prepare_recipe.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-montgomery-value-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-montgomery-value-owned-floor-20261011-02'")
a='  simp only [Nat.add_mod, Nat.mod_mul_mod]\n  rw [← Nat.add_mod]'
assert s.count(a)==1
s=s.replace(a,'  rw [Nat.add_mod, Nat.mod_mul_mod, Nat.mod_eq_of_lt word.toNat_lt, Nat.add_mod_mod]')
a='source_modulus_modulo_radix_is_actual_low_word, Nat.mod_eq_of_lt finite, ← Nat.add_mod]'
assert s.count(a)==1
s=s.replace(a,'source_modulus_modulo_radix_is_actual_low_word, Nat.mod_eq_of_lt finite, Nat.add_mod_mod]')
a='    rw [Nat.add_mod_right] at restored'
assert s.count(a)==1
s=s.replace(a,'    change (value - nullifierModulus + nullifierModulus) % nullifierModulus = value % nullifierModulus at restored\n    rw [Nat.add_mod_right] at restored')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained = "failedMontgomery = DIAG/'transfer-scalar-montgomery-value-20261011-01'\\nplan['pins'] += [pin(failedMontgomery/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarMontgomeryValue01.lean','project/ShielddSecurity/TransferScalarMontgomeryValue01.lean','runs/01-TransferScalarMontgomeryValue01/stdout.txt']]\\n"
s=s.replace('unique = {}',retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh symbolic Montgomery value refinement', 'Fresh02 proof-only nonlooping modular rewrites and explicit congrArg reduction, all thirteen contracts unchanged; failed01 warning/errors/full raw reports retained with zero credit. Fresh symbolic Montgomery value refinement')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
