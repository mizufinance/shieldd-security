from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-square-shift-20261011-02'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarSquareShift01.lean').read_text()
assert source.count('prefix')==3
source=source.replace('prefix','crossPrefix')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarSquareShift01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-square-shift-shape.json').write_bytes((OLD/'context/scalar-square-shift-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-square-shift-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-square-shift-owned-floor-20261011-03'")
at=s.index("plan['artifact_policy']")
extra="""failedShift=DIAG/'transfer-scalar-square-shift-20261011-02'
plan['pins'] += [pin(failedShift/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-shift-shape.json','handwritten/TransferScalarSquareShift01.lean','project/ShielddSecurity/TransferScalarSquareShift01.lean','runs/01-TransferScalarSquareShift01/stdout.txt']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'proof_local_reserved_token_renamed':True,'unchanged_definitions_and_contracts':True,'prior_raw_artifacts':13,'failed_credit':0})
