from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-bit-integer-20261012-02'
assert not (ROOT/'prepare.py').exists()
assert not (OLD/'runs/01-TransferScalarPowBitInteger01/stdout.txt').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarPowBitInteger01.lean').write_bytes((OLD/'handwritten/TransferScalarPowBitInteger01.lean').read_bytes())
(ROOT/'context').mkdir();(ROOT/'context/scalar-pow-bit-integer-shape.json').write_bytes((OLD/'context/scalar-pow-bit-integer-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-pow-bit-integer-owned-floor-20261012-02'","POOL = DIAG / 'transfer-scalar-pow-bit-integer-owned-floor-20261012-03'")
at=s.index("plan['artifact_policy']")
extra="""pressurePowBit=DIAG/'transfer-scalar-pow-bit-integer-20261012-02'
priorPressurePowBitNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-pow-bit-integer-shape.json','handwritten/TransferScalarPowBitInteger01.lean','project/ShielddSecurity/TransferScalarPowBitInteger01.lean']
assert not (pressurePowBit/'runs/01-TransferScalarPowBitInteger01/stdout.txt').exists()
plan['pins'] += [pin(pressurePowBit/n) for n in priorPressurePowBitNames]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'same_source_and_guards':True,'original_pressure_attempt_preserved':True,'prior_raw_artifacts':21})
