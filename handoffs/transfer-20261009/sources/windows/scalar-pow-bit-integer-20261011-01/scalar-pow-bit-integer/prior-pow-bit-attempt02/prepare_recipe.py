from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-bit-integer-20261012-01'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarPowBitInteger01.lean').read_text()
old='      rw [bounded_source_word_boolean_bit_has_exact_binary_digit word index bounded])'
new='      dsimp only\n      rw [bounded_source_word_boolean_bit_has_exact_binary_digit word index bounded])'
assert source.count(old)==1;source=source.replace(old,new)
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarPowBitInteger01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-pow-bit-integer-shape.json').write_bytes((OLD/'context/scalar-pow-bit-integer-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-pow-bit-integer-owned-floor-20261012-01'","POOL = DIAG / 'transfer-scalar-pow-bit-integer-owned-floor-20261012-02'")
at=s.index("plan['artifact_policy']")
extra="""failedPowBit=DIAG/'transfer-scalar-pow-bit-integer-20261012-01'
priorFailedPowBitNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-pow-bit-integer-shape.json','handwritten/TransferScalarPowBitInteger01.lean','project/ShielddSecurity/TransferScalarPowBitInteger01.lean','runs/01-TransferScalarPowBitInteger01/stdout.txt']
assert (failedPowBit/'runs/01-TransferScalarPowBitInteger01/stdout.txt').exists()
plan['pins'] += [pin(failedPowBit/n) for n in priorFailedPowBitNames]
if (failedPowBit/'project/ShielddSecurity/TransferScalarPowBitInteger01.olean').exists():
    plan['pins'].append(pin(failedPowBit/'project/ShielddSecurity/TransferScalarPowBitInteger01.olean'))
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'one_beta_simplification_added':True,'original_failed_stdout_retained':True,'guards_and_statements_unchanged':True})
