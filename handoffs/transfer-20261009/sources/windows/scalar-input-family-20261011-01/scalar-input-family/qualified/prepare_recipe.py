from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-input-family-20261011-03'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarInputFamily01.lean').read_text()
needle='  rw [source_32_byte_family_constructor_retains_exact_choice_success_projection] at projected';assert source.count(needle)==1
source=source.replace(needle,'  dsimp only at projected\n'+needle)
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarInputFamily01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-input-family-shape.json').write_bytes((OLD/'context/scalar-input-family-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-input-family-owned-floor-20261011-03'","POOL = DIAG / 'transfer-scalar-input-family-owned-floor-20261011-04'")
at=s.index("plan['artifact_policy']")
extra="""failedInputFamily=DIAG/'transfer-scalar-input-family-20261011-03'
plan['pins'] += [pin(failedInputFamily/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-input-family-shape.json','handwritten/TransferScalarInputFamily01.lean','project/ShielddSecurity/TransferScalarInputFamily01.lean','runs/01-TransferScalarInputFamily01/stdout.txt']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'proof_only_repair':'beta reduce congrArg observation before rewrite','unchanged_source_definitions_and_contracts':True,'prior_raw_artifacts':30,'prior_credit':0})
