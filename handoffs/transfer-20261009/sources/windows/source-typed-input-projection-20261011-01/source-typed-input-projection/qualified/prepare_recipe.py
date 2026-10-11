"""Proof-only targeted Function.comp reduction avoids unfolding scalar serialization."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-source-typed-input-projection-20261011-02/recipe_source.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-source-typed-input-projection-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-source-typed-input-projection-owned-floor-20261011-03'")
a='  rw [List.map_map]\n  rfl\n\ntheorem source_keys_are_exact_ordered_mathematical_montgomery_values'
assert s.count(a)==1
s=s.replace(a,'  rw [List.map_map]\n  simp only [Function.comp_def]\n\ntheorem source_keys_are_exact_ordered_mathematical_montgomery_values')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained02 = "failedProjection02 = DIAG/'transfer-source-typed-input-projection-20261011-02'\\nplan['pins'] += [pin(failedProjection02/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/source-projection-shape.json','handwritten/TransferSourceTypedInputProjection01.lean','project/ShielddSecurity/TransferSourceTypedInputProjection01.lean','runs/01-TransferSourceTypedInputProjection01/stdout.txt']]\\n"
s=s.replace('unique = {}',retained02+'unique = {}',1)
s=s.replace('Fresh02 proof-only reflexive closure of definitionally equal map composition, all six contracts unchanged; failed01 raw goal/reports/source retained with zero credit.', 'Fresh03 proof-only targeted Function.comp reduction after map rewrite, avoiding source scalar expansion. All six contracts unchanged; failed01 raw goal and failed02 finite-heartbeat timeout retained with zero credit. Guards unchanged.')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
