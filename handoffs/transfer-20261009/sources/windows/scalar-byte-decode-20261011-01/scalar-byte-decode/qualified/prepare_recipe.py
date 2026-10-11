"""Correct known reusable canonical-range lemma before any kernel invocation."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-scalar-byte-decode-20261011-01'
s=(old/'prepare_recipe.py').read_text()
a='TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_is_canonical words'
b='TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical words'
assert s.count(a)==1;s=s.replace(a,b).replace('transfer-scalar-byte-decode-owned-floor-20261011-01','transfer-scalar-byte-decode-owned-floor-20261011-02')
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
p=ROOT/'prepare.py';s=p.read_text();a="[Path(__file__), ROOT / 'prepare_recipe.py', runner";assert s.count(a)==1
s=s.replace(a,"[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner")
at=s.index("plan['artifact_policy']")
s=s[:at]+"unrunDecode=DIAG/'transfer-scalar-byte-decode-20261011-01'\nassert not (unrunDecode/'events.jsonl').exists()\nplan['pins'] += [pin(unrunDecode/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/decoder-shape.json','handwritten/TransferScalarByteDecode01.lean','project/ShielddSecurity/TransferScalarByteDecode01.lean']]\n"+s[at:]
p.write_text(s)
