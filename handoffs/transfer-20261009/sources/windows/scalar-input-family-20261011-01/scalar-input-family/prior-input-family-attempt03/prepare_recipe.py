from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-input-family-20261011-02'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarInputFamily01.lean').write_bytes((OLD/'handwritten/TransferScalarInputFamily01.lean').read_bytes())
(ROOT/'context').mkdir();(ROOT/'context/scalar-input-family-shape.json').write_bytes((OLD/'context/scalar-input-family-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-input-family-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-input-family-owned-floor-20261011-03'")
assert not (OLD/'runs/01-TransferScalarInputFamily01/stdout.txt').exists()
at=s.index("plan['artifact_policy']")
extra="""pressureInputFamily=DIAG/'transfer-scalar-input-family-20261011-02'
plan['pins'] += [pin(pressureInputFamily/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-input-family-shape.json','handwritten/TransferScalarInputFamily01.lean','project/ShielddSecurity/TransferScalarInputFamily01.lean']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'unchanged_source_proof_and_guards':True,'prior_raw_artifacts':19,'prior_credit':0,'second_attempt':'pre-Lean memory pressure','first':'withdrawn unrun preflight source'})
