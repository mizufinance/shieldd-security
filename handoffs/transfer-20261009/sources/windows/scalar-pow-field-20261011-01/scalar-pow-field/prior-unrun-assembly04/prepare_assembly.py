from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-inverse-correctness-endpoint-20261012-04/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-inverse-correctness-20261012-04'","CURRENT = DIAG / 'transfer-scalar-pow-field-20261012-03'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-inverse-correctness-checkpoint-20261012-04'","CHECKPOINT = DIAG / 'transfer-scalar-pow-field-checkpoint-20261012-03'"),
 ("MODULE = 'TransferScalarInverseCorrectness01'","MODULE = 'TransferScalarPowField01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-invert-field-endpoint-20261012-03'","manager_endpoint = DIAG / 'transfer-scalar-inverse-correctness-endpoint-20261012-04'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-invert-field-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-inverse-correctness-endpoint01.tar.xz'"),
 ('f2b15f75a23678c33590aad11df4c302a79575628dcc34ccc05adbcd5843db1e','c1cf8c43c246819d4ef31db22beef07b482fddccf0bb3c13ef8036f6b774a428'),
 ("'module': 'TransferScalarInvertField01'","'module': 'TransferScalarInverseCorrectness01'"),
 ("reference = {'scalar_invert_field':","reference = {'scalar_inverse_correctness':"),
 ('assert len(manager_reports) == 7','assert len(manager_reports) == 6'),
 ("manager_stdout = tar.extractfile('reports/fresh-7-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')"),
 ("archive = ROOT / 'portable-windows-scalar-inverse-correctness-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-pow-field-endpoint01.tar.xz'"),
 ("assert pool['objects'] == 202 and len(pool['inherited_public_reports']) == 1416","assert pool['objects'] == 204 and len(pool['inherited_public_reports']) == 1428")]:replace(a,b)
start=s.index('assert len(combined_reports)==1290');end=s.index('archive_source_cache={}',start)
merge="""assert len(combined_reports)==1422 and len(manager_selected)==203
bit_endpoint=DIAG/'transfer-scalar-pow-bit-integer-endpoint-20261012-03'
bit_archive=bit_endpoint/'portable-windows-scalar-pow-bit-integer-endpoint01.tar.xz'
assert pin(bit_archive)['sha256']=='32b7290c2eed3d3501e7824a6a8ef647d55d967fd9bffee4620d27f5501973c3'
with tarfile.open(bit_archive,'r:xz') as tar:
    bit_review=json.loads(tar.extractfile('review.json').read())
    bit_reference=json.loads(tar.extractfile('context/inherited-reference.json').read())
    bit_pool=json.loads(tar.extractfile('context/owned-composition-review.json').read())
    bit_plan=json.loads(tar.extractfile('qualified/plan.json').read())
    bit_events=[json.loads(line) for line in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    bit_stdout=tar.extractfile('reports/fresh-6-complete-declarations.txt').read().decode()
    bit_reports=m.audit(bit_stdout,bit_plan['targets'][0]['audit_names'])
assert len(bit_reports)==6 and bit_reports==bit_review['fresh_audits']==bit_events[-1]['result']['audits']
assert len(bit_pool['selected'])==162 and len(bit_pool['inherited_public_reports'])==1290
byModule={row['module']:row for row in manager_selected}
for row in bit_pool['selected']:
    original=byModule[row['module']]
    assert row['source']==original['source'] and row['object']==original['object']
    for key in ['source','object','copy']:assert pin(row[key]['path'])==row[key]
for name,report in bit_pool['inherited_public_reports'].items():assert combined_reports[name]==report
assert set(combined_reports).isdisjoint(bit_reports)
combined_reports.update(bit_reports)
manager_selected.append({'module':'TransferScalarPowBitInteger01','source':bit_plan['targets'][0]['source'],'object':bit_events[-1]['result']['objects'][0]})
assert len(combined_reports)==1428 and combined_reports==pool['inherited_public_reports']
assert len(manager_selected)==204
"""
s=s[:start]+merge+s[end:]
replace('carriers = [pin(manager_archive),fieldArchive]','carriers = [pin(manager_archive),pin(bit_archive)]')
replace("fieldOriginalPlan=DIAG/'transfer-prime-tree-closed-20261010-05/plan.json'\nassert json.loads(fieldOriginalPlan.read_text())['external_floor']==plan['external_floor']\nassert pin(fieldOriginalPlan) in plan['pins']","assert manager_plan['external_floor']==plan['external_floor']")
start=s.index("reference['field_foundation']=");end=s.index("dump(ROOT / 'inherited-reference.json', reference)",start)
ref="""reference['bit_integer_branch']={'archive':pin(bit_archive),'manifest':pin(bit_endpoint/'manifest.json'),'ancestors':bit_reference,'original_modules':163,'original_reports':1296,'shared_modules':162,'shared_reports':1290,'all_shared_original_source_object_and_complete_reports_identical':True}
reference['scope']='Complete204-module first owned root and1428 original complete reports: whole203-module inverse/prime branch and whole163-module bit-integer branch, with exact shared162 modules and1290 reports used once. Original field48-module packet unchanged; no ancestors replayed.'
"""
s=s[:start]+ref+s[end:]
replace("'prepare_recipe.py', 'prepare_recipe_from01.py', 'execute_bounded.py'","'prepare_recipe.py', 'execute_bounded.py'")
start=s.index('for attempt in [1,2,3]:');end=s.index("row=mapping['scalar_invert_field_source_shape']",start)
history="""for attempt in [1,2]:
    prior=DIAG/('transfer-scalar-pow-field-20261012-%02d'%attempt)
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean']
    if attempt==1:assert not (prior/'events.jsonl').exists()
    else:names+=['events.jsonl','runs/01-TransferScalarPowField01/stdout.txt']
    for name in names:
        row=pin(prior/name);assert row in plan['pins']
        add(prior/name,'prior-power-attempt%02d/'%attempt+name,'original unrun composition predecessor/warning-rejected attempt retained with full written stdout; no qualified result')
for key,filename in [('scalar_pow_field_source_shape','scalar-pow-field-shape.json'),('scalar_inverse_correctness_source_shape','scalar-inverse-correctness-shape.json')]:
    row=mapping[key];assert pin(row['path'])==row and row in plan['pins']
    add(row['path'],'context/'+filename,'exact source model and qualified prerequisite associations; native binding separate')
"""
s=s[:start]+history+s[end:]
start=s.index("    'scope': mapping['scope'] + '");end=s.index("}\ndump(ROOT / 'review.json'",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete theorem declarations derive the field exponent of each source bit/word step and full constant/variable source pow from the certified ONE initial value and reconstructed exponent integer. Two unused simplifier arguments removed; all statements/contracts/guards unchanged. Original20 prior raw artifacts retained including full warning-rejected output. Complete two-branch original identities deduplicated; no ancestors replayed. Native compiler/Choice/caller/full Transfer remain open.'"+s[end:]
s=s.replace('two-hundred-two-module','two-hundred-four-module').replace('1416 original inherited complete reports','1428 original inherited complete reports').replace('verified 1416 inherited reports','verified 1428 inherited reports')
s=s.replace("'status': 'SOURCE_PUBLIC_SCALAR_CONSTANTS_CANONICAL_RAW_AND_SERIALIZATION_QUALIFIED'","'status': 'SOURCE_SCALAR_POWER_EXACT_MATHEMATICAL_FIELD_VALUE_QUALIFIED'")
at=s.index("add(Path(__file__), 'assemble.py'")
s=s[:at]+"add(ROOT/'prepare_recipe_from03.py','prepare_recipe_from03.py','fresh assembly source repair derivation')\nadd(DIAG/'transfer-scalar-pow-field-endpoint-20261012-03/prepare_assembly.py','prior-assembly-setup03/prepare_assembly.py','original setup recipe failed before any assembly or evidence write; preserved unchanged')\n"+s[at:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-pow-field-checkpoint-20261012-03';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_reports':6,'inherited_reports':1428,'whole_owned_modules':204,'shared_original_modules':162,'shared_original_reports':1290,'prior_raw_artifacts':20,'assembly_not_run':True})
