"""Proof-only unfolding of wordBytes for two width rewrites; declarations unchanged."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'recipe_source.py').exists()
s=(DIAG/'transfer-scalar-little-endian-bytes-20261011-01/prepare_recipe.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-little-endian-bytes-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-little-endian-bytes-owned-floor-20261011-02'")
a='rw [List.length_append, typed_little_endian_encoding_has_exact_width, ih'
assert s.count(a)==1
s=s.replace(a,'rw [List.length_append, wordBytes, typed_little_endian_encoding_has_exact_width, ih')
a='      typed_little_endian_encoding_has_exact_width, ih]'
assert s.count(a)==1
s=s.replace(a,'      wordBytes, typed_little_endian_encoding_has_exact_width, ih]')
anchor="(ROOT/'prepare.py').write_text(s)"
assert s.count(anchor)==1
extra='''
retained = "failedBytes = DIAG/'transfer-scalar-little-endian-bytes-20261011-01'\\nplan['pins'] += [pin(failedBytes/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/serializer-byte-shape.json','handwritten/TransferScalarLittleEndianBytes01.lean','project/ShielddSecurity/TransferScalarLittleEndianBytes01.lean','runs/01-TransferScalarLittleEndianBytes01/stdout.txt']]\\n"
s=s.replace('unique = {}', retained+'unique = {}',1)
s=s.replace("[Path(__file__), ROOT / 'prepare_recipe.py', runner", "[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner",1)
s=s.replace('Fresh typed little-endian 32-byte serializer range/projection refinement', 'Fresh02 proof-only wordBytes wrapper unfolding at two exact-width rewrites; all fifteen declarations unchanged, failed01 full raw diagnostics retained with zero credit. Fresh typed little-endian 32-byte serializer range/projection refinement')
'''
s=s.replace(anchor,extra+'\n'+anchor)
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'))
