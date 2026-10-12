from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-wide-constructor-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarWideConstructor01.lean').write_bytes((OLD/'handwritten/TransferScalarWideConstructor01.lean').read_bytes())
(ROOT/'context').mkdir();(ROOT/'context/scalar-wide-constructor-shape.json').write_bytes((OLD/'context/scalar-wide-constructor-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-wide-constructor-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-wide-constructor-owned-floor-20261011-02'")
assert not (OLD/'runs/01-TransferScalarWideConstructor01/stdout.txt').exists()
at=s.index("plan['artifact_policy']")
extra="""pressureWide=DIAG/'transfer-scalar-wide-constructor-20261011-01'
plan['pins'] += [pin(pressureWide/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-wide-constructor-shape.json','handwritten/TransferScalarWideConstructor01.lean','project/ShielddSecurity/TransferScalarWideConstructor01.lean']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'unchanged_source_proof_and_guards':True,'failed_raw_artifacts':10,'failed_credit':0,'first_attempt':'pre-Lean memory pressure'})
