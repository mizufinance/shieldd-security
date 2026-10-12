from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-20261012-03'
assert not (ROOT/'prepare.py').exists() and not (OLD/'events.jsonl').exists()
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
source=(OLD/'handwritten/TransferScalarPowField01.lean').read_text()
old='import ShielddSecurity.TransferScalarInverseCorrectness01'
assert source.count(old)==1
source=source.replace(old,'import ShielddSecurity.TransferScalarFieldValues01')
(ROOT/'handwritten/TransferScalarPowField01.lean').write_text(source)
(ROOT/'context/scalar-pow-field-shape.json').write_bytes((OLD/'context/scalar-pow-field-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-03'","POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-04'")
old="'imports': ['ShielddSecurity.TransferScalarInverseCorrectness01', 'ShielddSecurity.TransferScalarPowBitInteger01']"
assert s.count(old)==1;s=s.replace(old,"'imports': ['ShielddSecurity.TransferScalarFieldValues01', 'ShielddSecurity.TransferScalarPowBitInteger01']")
extra="""unrunNarrowPower=DIAG/'transfer-scalar-pow-field-20261012-03'
assert not (unrunNarrowPower/'events.jsonl').exists()
unrunNarrowPowerNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean']
plan['pins'] += [pin(unrunNarrowPower/n) for n in unrunNarrowPowerNames]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_text(s)
print({'direct_import_narrowed_to_actual_field_operation_prerequisite':True,'six_theorem_statements_unchanged':True,'complete204_module1428_report_ancestry_preserved':True,'all_execution_guards_unchanged':True,'prior_unrun_raw_files':9})
