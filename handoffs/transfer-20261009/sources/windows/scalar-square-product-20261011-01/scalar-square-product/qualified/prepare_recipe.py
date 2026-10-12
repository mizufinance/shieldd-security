from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-square-product-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarSquareProduct01.lean').write_bytes((OLD/'handwritten/TransferScalarSquareProduct01.lean').read_bytes())
(ROOT/'context').mkdir();(ROOT/'context/scalar-square-product-shape.json').write_bytes((OLD/'context/scalar-square-product-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-square-product-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-square-product-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy']")
extra="""pressureSquareProduct=DIAG/'transfer-scalar-square-product-20261011-01'
priorSquareNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-product-shape.json','handwritten/TransferScalarSquareProduct01.lean','project/ShielddSecurity/TransferScalarSquareProduct01.lean']
if (pressureSquareProduct/'runs/01-TransferScalarSquareProduct01/stdout.txt').exists():
    priorSquareNames.append('runs/01-TransferScalarSquareProduct01/stdout.txt')
plan['pins'] += [pin(pressureSquareProduct/n) for n in priorSquareNames]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'same_handwritten_source_and_guards':True,'original_pressure_attempt_retained':True})
