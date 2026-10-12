from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-endpoint-20261012-03'
assert not (OLD/'assemble.py').exists() and not (ROOT/'prepare_assembly.py').exists()
s=(OLD/'prepare_assembly.py').read_text()
old='end=s.index("}\\n\\ndump(ROOT / \'review.json\'",start)'
new='end=s.index("}\\ndump(ROOT / \'review.json\'",start)'
assert s.count(old)==1;s=s.replace(old,new)
at=s.index("(ROOT/'assemble.py').write_text(s)")
extra="""at=s.index("add(Path(__file__), 'assemble.py'")
s=s[:at]+"add(ROOT/'prepare_recipe_from03.py','prepare_recipe_from03.py','fresh assembly source repair derivation')\\nadd(DIAG/'transfer-scalar-pow-field-endpoint-20261012-03/prepare_assembly.py','prior-assembly-setup03/prepare_assembly.py','original setup recipe failed before any assembly or evidence write; preserved unchanged')\\n"+s[at:]
"""
s=s[:at]+extra+s[at:]
(ROOT/'prepare_assembly.py').write_text(s)
print({'prior_setup_original_preserved':True,'only_new_recipe_changed':True})
