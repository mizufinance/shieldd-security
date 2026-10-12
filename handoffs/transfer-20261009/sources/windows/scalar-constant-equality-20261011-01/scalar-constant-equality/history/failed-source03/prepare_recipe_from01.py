from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-constant-equality-20261012-01'
assert not (OLD/'prepare.py').exists() and not (ROOT/'prepare_recipe.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarConstantEquality01.lean').write_bytes((OLD/'handwritten/TransferScalarConstantEquality01.lean').read_bytes())
s=(OLD/'prepare_recipe.py').read_text()
old='CtOption::new(tmp, !self.ct_eq(&Self::zero()))'
assert s.count(old)==1;s=s.replace(old,'CtOption::new(t0, !self.ct_eq(&Self::zero()))')
at=s.index("(ROOT/'prepare.py').write_text(s)")
extra="""extra=\"\"\"unpreparedEq=DIAG/'transfer-scalar-constant-equality-20261012-01'
assert not (unpreparedEq/'prepare.py').exists()
plan['pins'] += [pin(unpreparedEq/n) for n in ['prepare_recipe.py','handwritten/TransferScalarConstantEquality01.lean']]
plan['pins'].append(pin(ROOT/'prepare_recipe_from01.py'))
\"\"\"
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
"""
s=s[:at]+extra+s[at:]
(ROOT/'prepare_recipe.py').write_text(s)
print({'source_association_payload_identifier_corrected_to_actual_t0':True,'original_setup_files_retained':2,'theorem_source_unchanged':True})
