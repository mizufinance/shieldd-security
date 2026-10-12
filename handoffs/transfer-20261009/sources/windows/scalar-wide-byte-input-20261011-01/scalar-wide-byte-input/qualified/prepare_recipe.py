from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-wide-byte-input-20261011-01'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarWideByteInput01.lean').read_text()
needle='rw [List.length_drop, Vector.length_toList]; rfl';assert source.count(needle)==1
source=source.replace(needle,'rw [List.length_drop, Vector.length_toList]')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarWideByteInput01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-wide-byte-input-shape.json').write_bytes((OLD/'context/scalar-wide-byte-input-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-wide-byte-input-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-wide-byte-input-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy']")
extra="""failedWideBytes=DIAG/'transfer-scalar-wide-byte-input-20261011-01'
plan['pins'] += [pin(failedWideBytes/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-wide-byte-input-shape.json','handwritten/TransferScalarWideByteInput01.lean','project/ShielddSecurity/TransferScalarWideByteInput01.lean','runs/01-TransferScalarWideByteInput01/stdout.txt']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'proof_only_repair':'remove rfl after already-closed length rewrite','unchanged_source_definitions_and_contracts':True,'failed_raw_artifacts':11,'failed_credit':0})
