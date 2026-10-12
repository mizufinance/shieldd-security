from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-input-family-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (OLD/'events.jsonl').exists()
source=(OLD/'handwritten/TransferScalarInputFamily01.lean').read_text()
for condition in ['if_pos yes','if_neg yes']:
    needle='    simp only ['+condition+']\n    rfl';assert source.count(needle)==1
    source=source.replace(needle,'    simp only ['+condition+'] <;> rfl')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarInputFamily01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-input-family-shape.json').write_bytes((OLD/'context/scalar-input-family-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-input-family-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-input-family-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy']")
extra="""unrunInputFamily=DIAG/'transfer-scalar-input-family-20261011-01'
assert not (unrunInputFamily/'events.jsonl').exists()
plan['pins'] += [pin(unrunInputFamily/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-input-family-shape.json','handwritten/TransferScalarInputFamily01.lean','project/ShielddSecurity/TransferScalarInputFamily01.lean']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'preflight_proof_only_repair':'conditional finishing rfl after simplification','unchanged_source_definitions_and_contracts':True,'withdrawn_unrun_raw_artifacts':9,'withdrawn_credit':0})
