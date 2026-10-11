"""Proof-only numeral rewrite and actual List lemma repairs; declarations unchanged."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-carry-schedule-20261011-01/prepare_recipe.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-carry-schedule-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-carry-schedule-owned-floor-20261011-02'")
a='    _ = _ := by rw [Nat.div_eq_of_lt low.toNat_lt, Nat.zero_add]'
assert s.count(a)==1
s=s.replace(a,'    _ = _ := by\n      have lowBound : low.toNat < radix64 := low.toNat_lt\n      rw [Nat.div_eq_of_lt lowBound, Nat.zero_add]')
a='List.length_eq_zero.mp length.symm'
assert s.count(a)==1
s=s.replace(a,'List.eq_nil_of_length_eq_zero length.symm')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained = "failedCarry = DIAG/'transfer-scalar-carry-schedule-20261011-01'\\nplan['pins'] += [pin(failedCarry/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCarrySchedule01.lean','project/ShielddSecurity/TransferScalarCarrySchedule01.lean','runs/01-TransferScalarCarrySchedule01/stdout.txt']]\\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh symbolic carry schedule and low-limb quotient proof', 'Fresh02 proof-only radix/numeral rewrite and actual List lemma fixes; all seven declaration contracts unchanged and failed01 raw diagnostics retained with zero credit. Fresh symbolic carry schedule and low-limb quotient proof')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
