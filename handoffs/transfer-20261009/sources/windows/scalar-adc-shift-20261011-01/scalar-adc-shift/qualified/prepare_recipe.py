"""Proof-only explicit radix and BitVec one notation; no contract or guard changes."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-adc-shift-20261011-01/prepare_recipe.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-adc-shift-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-adc-shift-owned-floor-20261011-02'")
a='  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]'
assert s.count(a)==1
s=s.replace(a,a+'\n  rfl')
a='(1 : BitVec 128) * BitVec.ofNat 128 b.toNat'
assert s.count(a)==1
s=s.replace(a,'(1#128) * BitVec.ofNat 128 b.toNat')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained = "failedAdc = DIAG/'transfer-scalar-adc-shift-20261011-01'\\nplan['pins'] += [pin(failedAdc/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarAdcShift01.lean','project/ShielddSecurity/TransferScalarAdcShift01.lean','runs/01-TransferScalarAdcShift01/stdout.txt']]\\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh fixed-shift/cast and widened ADC equations', 'Fresh02 proof-only explicit radix reflexivity and width-indexed BitVec one notation; all eight declaration contracts unchanged, failed01 raw diagnostics retained with zero credit. Fresh fixed-shift/cast and widened ADC equations')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
