from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-inverse-correctness-endpoint-20261012-04/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-inverse-correctness-20261012-04'","CURRENT = DIAG / 'transfer-scalar-public-orders-20261012-02'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-inverse-correctness-checkpoint-20261012-04'","CHECKPOINT = DIAG / 'transfer-scalar-public-orders-checkpoint-20261012-02'"),
 ("MODULE = 'TransferScalarInverseCorrectness01'","MODULE = 'TransferScalarPublicOrders01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-invert-field-endpoint-20261012-03'","manager_endpoint = DIAG / 'transfer-scalar-inverse-correctness-endpoint-20261012-04'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-invert-field-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-inverse-correctness-endpoint01.tar.xz'"),
 ('f2b15f75a23678c33590aad11df4c302a79575628dcc34ccc05adbcd5843db1e','c1cf8c43c246819d4ef31db22beef07b482fddccf0bb3c13ef8036f6b774a428'),
 ("'module': 'TransferScalarInvertField01'","'module': 'TransferScalarInverseCorrectness01'"),
 ("reference = {'scalar_invert_field':","reference = {'scalar_inverse_correctness':"),
 ('assert len(manager_reports) == 7','assert len(manager_reports) == 6'),
 ("manager_stdout = tar.extractfile('reports/fresh-7-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')"),
 ("archive = ROOT / 'portable-windows-scalar-inverse-correctness-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-public-orders-endpoint01.tar.xz'"),
 ('assert len(fresh) == 6','assert len(fresh) == 7'),
 ("declaration_kinds.count('theorem') == 6","declaration_kinds.count('theorem') == 7"),
 ("add(stdout, 'reports/fresh-6-complete-declarations.txt'","add(stdout, 'reports/fresh-7-complete-declarations.txt'"),
 ("assert pool['objects'] == 202 and len(pool['inherited_public_reports']) == 1416","assert pool['objects'] == 203 and len(pool['inherited_public_reports']) == 1422")]:replace(a,b)
start=s.index('assert len(combined_reports)==1290');end=s.index('archive_source_cache={}',start)
s=s[:start]+"assert len(combined_reports)==1422 and combined_reports==pool['inherited_public_reports']\nassert len(manager_selected)==203\n\n"+s[end:]
replace('carriers = [pin(manager_archive),fieldArchive]','carriers = [pin(manager_archive)]')
replace("fieldOriginalPlan=DIAG/'transfer-prime-tree-closed-20261010-05/plan.json'\nassert json.loads(fieldOriginalPlan.read_text())['external_floor']==plan['external_floor']\nassert pin(fieldOriginalPlan) in plan['pins']","assert manager_plan['external_floor']==plan['external_floor']")
start=s.index("reference['field_foundation']=");end=s.index("dump(ROOT / 'inherited-reference.json', reference)",start)
s=s[:start]+"reference['scope']='Complete203-module first owned root and1422 original complete reports: whole qualified inverse/prime/word branch reused once. Original field48-module packet unchanged; no ancestors replayed.'\n"+s[end:]
replace("'prepare_recipe.py', 'prepare_recipe_from01.py', 'execute_bounded.py'","'prepare_recipe.py', 'execute_bounded.py'")
start=s.index('for attempt in [1,2,3]:');end=s.index("row=mapping['scalar_invert_field_source_shape']",start)
history="""unprepared=DIAG/'transfer-scalar-public-orders-20261012-01'
assert not (unprepared/'plan.json').exists() and not (unprepared/'events.jsonl').exists()
for name in ['prepare_recipe.py','prepare.py','execute_bounded.py','source-mapping.json','context/scalar-public-orders-shape.json','handwritten/TransferScalarPublicOrders01.lean','project/ShielddSecurity/TransferScalarPublicOrders01.lean']:
    row=pin(unprepared/name);assert row in plan['pins']
    add(unprepared/name,'prior-orders-setup01/'+name,'original setup recipe stopped before plan/execution; source unchanged and all actual written files preserved')
priorComposition=DIAG/'transfer-scalar-public-orders-owned-floor-20261012-01/composition-review.json'
assert pin(priorComposition) in plan['pins']
add(priorComposition,'prior-orders-setup01/composition-review.json','original prepared identity composition before setup failure; no execution or new qualified result')
for key,filename in [('scalar_public_orders_source_shape','scalar-public-orders-shape.json'),('scalar_inverse_correctness_source_shape','scalar-inverse-correctness-shape.json')]:
    row=mapping[key];assert pin(row['path'])==row and row in plan['pins']
    add(row['path'],'context/'+filename,'exact public constants/qualified Lucas/order source identities; mathematical field interpretation, native binding separate')
"""
s=s[:start]+history+s[end:]
start=s.index("    'scope': mapping['scope'] + '");end=s.index("}\ndump(ROOT / 'review.json'",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete theorem declarations. Generic checked Lucas certificate derives generator order; exact public source generator order p-1; bounded binary checks derive root/DELTA generator powers, root/inverse order2^32, and DELTA full odd-part order. Exact original prime tree used unchanged without replay. All8 original setup artifacts retained; setup omission repaired before any prior Lean execution. Native compiler/Choice/library/caller/full Transfer remain open.'"+s[end:]
s=s.replace('two-hundred-two-module','two-hundred-three-module').replace('1416 original inherited complete reports','1422 original inherited complete reports').replace('verified 1416 inherited reports','verified 1422 inherited reports')
s=s.replace("'status': 'SOURCE_PUBLIC_SCALAR_CONSTANTS_CANONICAL_RAW_AND_SERIALIZATION_QUALIFIED'","'status': 'SOURCE_PUBLIC_SCALAR_CONSTANTS_EXACT_GENERATOR_ROOT_AND_DELTA_ORDERS_QUALIFIED'")
s=s.replace("'rejected_attempts': 1, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0","'rejected_attempts': 0, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 1")
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-public-orders-checkpoint-20261012-02';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_theorems':7,'whole_owned_modules':203,'inherited_complete_reports':1422,'original_setup_artifacts':8,'assembly_not_run':True})
