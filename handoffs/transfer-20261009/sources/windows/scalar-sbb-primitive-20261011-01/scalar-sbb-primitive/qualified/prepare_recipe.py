"""Proof-only reduction of the second conditional in each SBB branch."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-sbb-primitive-20261011-01/prepare_recipe.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-sbb-primitive-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-sbb-primitive-owned-floor-20261011-02'")
a='    · change (((2 ^ 128 - (b.toNat + borrowBit borrow)) + a.toNat) % 2 ^ 64)'
assert s.count(a)==1
s=s.replace(a,'    · rw [if_pos underflow]\n      change (((2 ^ 128 - (b.toNat + borrowBit borrow)) + a.toNat) % 2 ^ 64)')
a='    · change (a.toNat - (b.toNat + borrowBit borrow)) % 2 ^ 64 + b.toNat'
assert s.count(a)==1
s=s.replace(a,'    · rw [if_neg underflow]\n      change (a.toNat - (b.toNat + borrowBit borrow)) % 2 ^ 64 + b.toNat')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained = "failedSbb = DIAG/'transfer-scalar-sbb-primitive-20261011-01'\\nplan['pins'] += [pin(failedSbb/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarSbbPrimitive01.lean','project/ShielddSecurity/TransferScalarSbbPrimitive01.lean','runs/01-TransferScalarSbbPrimitive01/stdout.txt']]\\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh reachable-mask single-word SBB arithmetic refinement', 'Fresh02 proof-only reduction of second branch conditional; all nine declarations unchanged, failed01 full raw diagnostics retained with zero credit. Fresh reachable-mask single-word SBB arithmetic refinement')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
