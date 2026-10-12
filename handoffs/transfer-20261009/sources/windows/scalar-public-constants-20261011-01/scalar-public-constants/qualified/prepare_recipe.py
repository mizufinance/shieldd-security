from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-public-constants-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarPublicConstants01.lean').write_bytes((OLD/'handwritten/TransferScalarPublicConstants01.lean').read_bytes())
(ROOT/'context').mkdir();(ROOT/'context/scalar-public-constants-shape.json').write_bytes((OLD/'context/scalar-public-constants-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-public-constants-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-public-constants-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy']")
extra="""pressureConstants=DIAG/'transfer-scalar-public-constants-20261011-01'
priorConstantNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-public-constants-shape.json','handwritten/TransferScalarPublicConstants01.lean','project/ShielddSecurity/TransferScalarPublicConstants01.lean']
if (pressureConstants/'runs/01-TransferScalarPublicConstants01/stdout.txt').exists():
    priorConstantNames.append('runs/01-TransferScalarPublicConstants01/stdout.txt')
plan['pins'] += [pin(pressureConstants/n) for n in priorConstantNames]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'same_source_and_guards':True,'original_pressure_attempt_retained':True})
