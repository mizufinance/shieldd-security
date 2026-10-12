from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-20261012-02'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
source=(OLD/'handwritten/TransferScalarPowField01.lean').read_text()
assert source.count(', Nat.mod_mod')==2
source=source.replace(', Nat.mod_mod','')
(ROOT/'handwritten/TransferScalarPowField01.lean').write_text(source)
(ROOT/'context/scalar-pow-field-shape.json').write_bytes((OLD/'context/scalar-pow-field-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-02'","POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-03'")
extra="""failedPower=DIAG/'transfer-scalar-pow-field-20261012-02'
failedPowerNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean','events.jsonl','runs/01-TransferScalarPowField01/stdout.txt']
plan['pins'] += [pin(failedPower/n) for n in failedPowerNames]
"""
at=s.index("plan['artifact_policy']")
s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_text(s)
print({'repair':'Remove only two unused simp arguments; all six theorem statements and guarded execution unchanged','failed_original_raw_files':11})
