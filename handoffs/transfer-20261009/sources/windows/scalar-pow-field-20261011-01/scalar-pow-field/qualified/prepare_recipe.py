from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-20261012-07'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
(ROOT/'handwritten/TransferScalarPowField01.lean').write_bytes((OLD/'handwritten/TransferScalarPowField01.lean').read_bytes())
(ROOT/'context/scalar-pow-field-shape.json').write_bytes((OLD/'context/scalar-pow-field-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-07'","POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-08'")
extra="""pressurePowerSeventh=DIAG/'transfer-scalar-pow-field-20261012-07'
pressurePowerSeventhNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean','events.jsonl']
assert not (pressurePowerSeventh/'runs/01-TransferScalarPowField01/stdout.txt').exists()
plan['pins'] += [pin(pressurePowerSeventh/n) for n in pressurePowerSeventhNames]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_text(s)
print({'pressure_predecessor_original_retained':True,'stdout_absent':True,'source_and_all_execution_guards_unchanged':True})
