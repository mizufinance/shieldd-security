from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-canonical-neg-20261011-02'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarCanonicalNeg01.lean').write_bytes((OLD/'handwritten/TransferScalarCanonicalNeg01.lean').read_bytes())
(ROOT/'context').mkdir();(ROOT/'context/scalar-canonical-neg-shape.json').write_bytes((OLD/'context/scalar-canonical-neg-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-canonical-neg-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-canonical-neg-owned-floor-20261011-03'")
assert not (OLD/'runs/01-TransferScalarCanonicalNeg01/stdout.txt').exists()
at=s.index("plan['artifact_policy']")
extra="""pressureNeg=DIAG/'transfer-scalar-canonical-neg-20261011-02'
plan['pins'] += [pin(pressureNeg/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-canonical-neg-shape.json','handwritten/TransferScalarCanonicalNeg01.lean','project/ShielddSecurity/TransferScalarCanonicalNeg01.lean']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'unchanged_source_proof_and_guards':True,'failed_raw_artifacts':21,'failed_credit':0,'second_attempt':'pre-Lean memory pressure'})
