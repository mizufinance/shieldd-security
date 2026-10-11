"""Proof-only normalization of actual returned difference projections before borrow cases."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-masked-normalization-20261011-01/prepare_recipe.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-masked-normalization-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-masked-normalization-owned-floor-20261011-02'")
a='  cases final : difference.2 with'
assert s.count(a)==1
b='''  change packWords difference.1 + nullifierModulus + borrowBit false =
    packWords words + radix64 ^ 4 * borrowBit difference.2 at conserved
  change difference.2 = true ↔ packWords words < nullifierModulus at underflow
  cases final : difference.2 with'''
s=s.replace(a,b)
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained = "failedNormalization = DIAG/'transfer-scalar-masked-normalization-20261011-01'\\nplan['pins'] += [pin(failedNormalization/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarMaskedNormalization01.lean','project/ShielddSecurity/TransferScalarMaskedNormalization01.lean','runs/01-TransferScalarMaskedNormalization01/stdout.txt']]\\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh source-shaped masked SBB/ADC normalization join', 'Fresh02 proof-only actual returned-difference projection normalization before borrow cases; all ten contracts unchanged, failed01 full raw diagnostics retained with zero credit. Fresh source-shaped masked SBB/ADC normalization join')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
