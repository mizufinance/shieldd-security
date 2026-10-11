"""Proof-only modulo normalization repair, with all earlier failures and byte pins retained."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-word-primitives-20261011-02/recipe_source.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-word-primitives-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-word-primitives-owned-floor-20261011-03'")
a='rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mod_add_mod, Nat.add_mod_mod]'
assert s.count(a)==1
s=s.replace(a,'simp only [Nat.mod_add_mod, Nat.add_mod_mod, Nat.mod_mul_mod, Nat.mul_mod_mod]')
a='change ret.toNat % 2 ^ 64 + radix64 * ((ret.toNat / radix64) % 2 ^ 64) = ret.toNat'
assert s.count(a)==1
s=s.replace(a,'change ret.toNat % radix64 + radix64 * ((ret.toNat / radix64) % radix64) = ret.toNat')
a="wordContext = [pin(ROOT/'capture_source.py')] + [pin(p) for p in sorted((ROOT/'context').iterdir()) if p.is_file()]"
assert s.count(a)==1
s=s.replace(a,"wordContext = [pin(DIAG/'transfer-scalar-word-primitives-20261011-02/capture_source.py')] + [pin(p) for p in sorted((DIAG/'transfer-scalar-word-primitives-20261011-02/context').iterdir()) if p.is_file()]")
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained02 = "failedWords = DIAG/'transfer-scalar-word-primitives-20261011-02'\\nplan['pins'] += [pin(failedWords/n) for n in ['capture_source.py','prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarWordPrimitives01.lean','project/ShielddSecurity/TransferScalarWordPrimitives01.lean','runs/01-TransferScalarWordPrimitives01/stdout.txt']]\\n"
s=s.replace('unique = {}', retained02+'unique = {}',1)
s=s.replace('Fresh finite word and widened MAC source arithmetic refinement', 'Fresh03 proof-only modulo normalization repairs leave all ten declaration statements unchanged; failed02 raw diagnostics retained with zero credit. Fresh finite word and widened MAC source arithmetic refinement')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
