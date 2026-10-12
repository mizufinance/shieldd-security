from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-square-diagonal-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarSquareDiagonal01.lean').write_bytes((OLD/'handwritten/TransferScalarSquareDiagonal01.lean').read_bytes())
(ROOT/'context').mkdir();(ROOT/'context/scalar-square-diagonal-shape.json').write_bytes((OLD/'context/scalar-square-diagonal-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-square-diagonal-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-square-diagonal-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy']")
extra="""pressureDiagonal=DIAG/'transfer-scalar-square-diagonal-20261011-01'
assert not (pressureDiagonal/'runs/01-TransferScalarSquareDiagonal01/stdout.txt').exists()
plan['pins'] += [pin(pressureDiagonal/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-diagonal-shape.json','handwritten/TransferScalarSquareDiagonal01.lean','project/ShielddSecurity/TransferScalarSquareDiagonal01.lean']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'same_handwritten_source_and_guards':True,'prior_raw_artifacts':10,'no_prior_Lean_stdout':True})
