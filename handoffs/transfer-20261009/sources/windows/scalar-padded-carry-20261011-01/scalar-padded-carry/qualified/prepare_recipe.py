"""Proof-only reduction of local padded-round bindings before exact ADC rewrite."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-padded-carry-20261011-02/recipe_source.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-padded-carry-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-padded-carry-owned-floor-20261011-03'")
a='  rw [taken, dropped, rest, List.headD_cons,\n    TransferScalarAdcShift01.zero_upper_limb_adc_retains_carry_without_overflow]'
assert s.count(a)==1
s=s.replace(a,'  rw [taken, dropped, rest, List.headD_cons]\n  dsimp only\n  rw [TransferScalarAdcShift01.zero_upper_limb_adc_retains_carry_without_overflow]')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained02 = "failedPadded02 = DIAG/'transfer-scalar-padded-carry-20261011-02'\\nplan['pins'] += [pin(failedPadded02/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarPaddedCarry01.lean','project/ShielddSecurity/TransferScalarPaddedCarry01.lean','runs/01-TransferScalarPaddedCarry01/stdout.txt']]\\n"
s=s.replace('unique = {}',retained02+'unique = {}',1)
s=s.replace('Fresh02 identical source after failed01 physical-memory monitor stopped its owned job.', 'Fresh03 proof-only local let reduction before exact zero-upper ADC rewrite; all six contracts unchanged. Failed02 full raw let-rewrite error/reports retained with zero credit. Fresh02 identical source after failed01 physical-memory monitor stopped its owned job.')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
