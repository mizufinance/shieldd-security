"""Proof-only reflexive closure after ordered input map composition rewrite."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-source-typed-input-projection-20261011-01/prepare_recipe.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-source-typed-input-projection-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-source-typed-input-projection-owned-floor-20261011-02'")
a='  rw [List.map_map]\n\ntheorem source_keys_are_exact_ordered_mathematical_montgomery_values'
assert s.count(a)==1
s=s.replace(a,'  rw [List.map_map]\n  rfl\n\ntheorem source_keys_are_exact_ordered_mathematical_montgomery_values')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained = "failedProjection = DIAG/'transfer-source-typed-input-projection-20261011-01'\\nplan['pins'] += [pin(failedProjection/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/source-projection-shape.json','handwritten/TransferSourceTypedInputProjection01.lean','project/ShielddSecurity/TransferSourceTypedInputProjection01.lean','runs/01-TransferSourceTypedInputProjection01/stdout.txt']]\\n"
s=s.replace('unique = {}',retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh concrete source-shaped ordered all-slot typed input configuration', 'Fresh02 proof-only reflexive closure of definitionally equal map composition, all six contracts unchanged; failed01 raw goal/reports/source retained with zero credit. Fresh concrete source-shaped ordered all-slot typed input configuration')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
