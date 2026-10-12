from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-wide-constructor-20261011-02'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarWideConstructor01.lean').read_text()
needle='    congr 1\n';assert source.count(needle)==1
source=source.replace(needle,'    apply congrArg (fun value : Nat => value % nullifierModulus)\n')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarWideConstructor01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-wide-constructor-shape.json').write_bytes((OLD/'context/scalar-wide-constructor-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-wide-constructor-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-wide-constructor-owned-floor-20261011-03'")
at=s.index("plan['artifact_policy']")
extra="""failedWide=DIAG/'transfer-scalar-wide-constructor-20261011-02'
plan['pins'] += [pin(failedWide/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-wide-constructor-shape.json','handwritten/TransferScalarWideConstructor01.lean','project/ShielddSecurity/TransferScalarWideConstructor01.lean','runs/01-TransferScalarWideConstructor01/stdout.txt']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'proof_only_repair':'explicit congrArg for modulo context','unchanged_source_definitions_and_contracts':True,'failed_raw_artifacts':21,'failed_credit':0})
