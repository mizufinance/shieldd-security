from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-invert-field-20261012-02'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarInvertField01.lean').read_text()
assert source.count('refine ⟨exponent, read, ?_⟩')==1
assert source.count('Nat.mod_mul_mod, ← Nat.pow_add]')==1
source=source.replace('refine ⟨exponent, read, ?_⟩','refine ⟨exponent, rfl, ?_⟩').replace('Nat.mod_mul_mod, ← Nat.pow_add]','Nat.mod_mul_mod, Nat.mul_mod_mod, ← Nat.pow_add]')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarInvertField01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-invert-field-shape.json').write_bytes((OLD/'context/scalar-invert-field-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-invert-field-owned-floor-20261012-02'","POOL = DIAG / 'transfer-scalar-invert-field-owned-floor-20261012-03'")
at=s.index("plan['artifact_policy']")
extra="""failedInvertField=DIAG/'transfer-scalar-invert-field-20261012-02'
priorFailedInvertFieldNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-field-shape.json','handwritten/TransferScalarInvertField01.lean','project/ShielddSecurity/TransferScalarInvertField01.lean','runs/01-TransferScalarInvertField01/stdout.txt']
assert (failedInvertField/'runs/01-TransferScalarInvertField01/stdout.txt').exists()
plan['pins'] += [pin(failedInvertField/n) for n in priorFailedInvertFieldNames]
if (failedInvertField/'project/ShielddSecurity/TransferScalarInvertField01.olean').exists():
    plan['pins'].append(pin(failedInvertField/'project/ShielddSecurity/TransferScalarInvertField01.olean'))
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'proof_script_repairs':2,'original_failed_stdout_retained':True,'guards_unchanged':True})
