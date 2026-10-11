"""Keep primitive01 unrun; prepare fresh source association without absent metadata assumption."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-word-primitives-20261011-01/prepare_recipe.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-word-primitives-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-word-primitives-owned-floor-20261011-02'")
s=s.replace('with source checksum and exact Cargo.lock package identity','with raw source identity and optional cached archive authentication against exact Cargo.lock')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained = "unrunWords = DIAG/'transfer-scalar-word-primitives-20261011-01'\\nplan['pins'] += [pin(unrunWords/n) for n in ['capture_source.py','prepare_recipe.py','prepare.py','handwritten/TransferScalarWordPrimitives01.lean']]\\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
