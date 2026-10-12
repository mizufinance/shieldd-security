from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-invert-field-20261012-01'
assert not (ROOT/'prepare.py').exists()
assert not (OLD/'runs/01-TransferScalarInvertField01/stdout.txt').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarInvertField01.lean').write_bytes((OLD/'handwritten/TransferScalarInvertField01.lean').read_bytes())
(ROOT/'context').mkdir();(ROOT/'context/scalar-invert-field-shape.json').write_bytes((OLD/'context/scalar-invert-field-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-invert-field-owned-floor-20261012-01'","POOL = DIAG / 'transfer-scalar-invert-field-owned-floor-20261012-02'")
at=s.index("plan['artifact_policy']")
extra="""pressureInvertField=DIAG/'transfer-scalar-invert-field-20261012-01'
priorInvertFieldNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-field-shape.json','handwritten/TransferScalarInvertField01.lean','project/ShielddSecurity/TransferScalarInvertField01.lean']
assert not (pressureInvertField/'runs/01-TransferScalarInvertField01/stdout.txt').exists()
plan['pins'] += [pin(pressureInvertField/n) for n in priorInvertFieldNames]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'same_source_and_guards':True,'original_pressure_attempt_retained':True,'prior_raw_artifacts':10})
