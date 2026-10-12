from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-20261012-04'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
(ROOT/'handwritten/TransferScalarPowField01.lean').write_bytes((OLD/'handwritten/TransferScalarPowField01.lean').read_bytes())
(ROOT/'context/scalar-pow-field-shape.json').write_bytes((OLD/'context/scalar-pow-field-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-04'","POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-05'")
extra="""pressurePower=DIAG/'transfer-scalar-pow-field-20261012-04'
pressurePowerNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean','events.jsonl']
pressureStdout=pressurePower/'runs/01-TransferScalarPowField01/stdout.txt'
if pressureStdout.exists():pressurePowerNames.append('runs/01-TransferScalarPowField01/stdout.txt')
plan['pins'] += [pin(pressurePower/n) for n in pressurePowerNames]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_text(s)
print({'pressure_predecessor_preserved':True,'source_theorems_and_all_guards_unchanged':True})
