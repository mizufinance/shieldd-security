"""Fresh identical source retry after owned memory-pressure stop; strict guards unchanged."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
failed=DIAG/'transfer-scalar-padded-carry-20261011-01'
events=[json.loads(x) for x in (failed/'events.jsonl').read_text().splitlines()]
assert events[-1]['result']['status']=='failed' and events[-1]['result']['reason']=='Physical memory pressure'
assert not (failed/'runs/01-TransferScalarPaddedCarry01/stdout.txt').exists()
assert not (ROOT/'recipe_source.py').exists()
s=(failed/'prepare_recipe.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-padded-carry-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-padded-carry-owned-floor-20261011-02'")
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained = "pressureStopped = DIAG/'transfer-scalar-padded-carry-20261011-01'\\nplan['pins'] += [pin(pressureStopped/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarPaddedCarry01.lean','project/ShielddSecurity/TransferScalarPaddedCarry01.lean']]\\n"
s=s.replace('unique = {}',retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh explicit source padded MAC/ADC schedule', 'Fresh02 identical source after failed01 physical-memory monitor stopped its owned job. Failed01 exact source/plan/events retained, no stdout saved before interruption, zero proof/control credit. All guards unchanged. Fresh explicit source padded MAC/ADC schedule')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
assert (ROOT/'handwritten/TransferScalarPaddedCarry01.lean').read_bytes()==(failed/'handwritten/TransferScalarPaddedCarry01.lean').read_bytes()
