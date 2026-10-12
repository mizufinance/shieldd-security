from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
upstream=DIAG/'transfer-scalar-inverse-correctness-20261012-04'
bits=DIAG/'transfer-scalar-pow-bit-integer-20261012-03'
for producer in [upstream,bits]:
    events=[json.loads(line) for line in (producer/'events.jsonl').read_text().splitlines()]
    assert len(events)==2 and events[-1]['result']['status']=='passed'
(ROOT/'context').mkdir()
(ROOT/'context/scalar-pow-field-shape.json').write_text(json.dumps({
 'scope':'Actual modeled constant/variable bit step square/multiply outputs derive field exponents; symbolic bit/word folds and exact reconstructed little-endian integer derive complete source pow/pow_vartime mathematical powers from source ONE. Final endpoints have no caller desired field-power premise. Shared162-module word foundation retained once and exact source/object/report equality checked across both qualified branches. Native Choice/compiler/caller/full Transfer remain separate.',
 'power_source':pin(DIAG/'transfer-scalar-pow-invariant-20261011-01/handwritten/TransferScalarPowInvariant01.lean'),
 'integer_exponent_source':pin(bits/'handwritten/TransferScalarPowBitInteger01.lean'),
 'field_operation_source':pin(DIAG/'transfer-scalar-field-values-20261012-01/handwritten/TransferScalarFieldValues01.lean')
},indent=2,sort_keys=True)+'\n')
s=(upstream/'prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-invert-field-20261012-03'","UPSTREAM = DIAG / 'transfer-scalar-inverse-correctness-20261012-04'"),
 ("POOL = DIAG / 'transfer-scalar-inverse-correctness-owned-floor-20261012-04'","POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-01'"),
 ("MODULE = 'TransferScalarInverseCorrectness01'","MODULE = 'TransferScalarPowField01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarInvertField01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarInverseCorrectness01/stdout.txt'"),
 ('assert len(current) == 7','assert len(current) == 6'),
 ("records.append(('TransferScalarInvertField01'","records.append(('TransferScalarInverseCorrectness01'"),
 ("'handwritten/TransferScalarInvertField01.lean', 'project/ShielddSecurity/TransferScalarInvertField01.lean'","'handwritten/TransferScalarInverseCorrectness01.lean', 'project/ShielddSecurity/TransferScalarInverseCorrectness01.lean'"),
 ("'imports': ['ShielddSecurity.TransferScalarInvertField01', 'ShielddSecurity.FieldPrimeNode38', 'Mathlib.Data.Fintype.Units', 'Mathlib.GroupTheory.OrderOfElement']","'imports': ['ShielddSecurity.TransferScalarInverseCorrectness01', 'ShielddSecurity.TransferScalarPowBitInteger01']")]:replace(a,b)
replace('assert len(records) == 162 and len(audits) == 1290','assert len(records) == 203 and len(audits) == 1422')
start=s.index("\nfieldEndpoint=DIAG/'transfer-field-cardinality-endpoint-20261010-02'",s.index('assert len(records) == 203'))
end=s.index('\nPOOL.mkdir()',start)
merge="""
bits=DIAG/'transfer-scalar-pow-bit-integer-20261012-03'
bitPlan=json.loads((bits/'plan.json').read_text()); bitPool=json.loads(Path(bitPlan['owned_import_pool']['path']).read_text())
assert bitPool['objects']==162 and len(bitPool['inherited_public_reports'])==1290
mainByModule={name:(source,obj) for name,source,obj in records}
assert set(bitPool['inherited_public_reports'])<=set(audits)
for name,report in bitPool['inherited_public_reports'].items():assert audits[name]==report
for row in bitPool['selected']:
    assert mainByModule[row['module']]==(row['source'],row['object'])
    assert pin(row['copy']['path'])==row['copy']
bitEvents=[json.loads(line) for line in (bits/'events.jsonl').read_text().splitlines()]
assert len(bitEvents)==2 and bitEvents[-1]['result']['status']=='passed'
bitTarget=bitPlan['targets'][0];bitResult=bitEvents[-1]['result']
bitStdout=bits/'runs/01-TransferScalarPowBitInteger01/stdout.txt'
bitReports=m.audit(bitStdout.read_text(),bitTarget['audit_names'])
assert len(bitReports)==6 and bitReports==bitResult['audits']
assert pin(bitStdout)==bitResult['stdout'] and set(audits).isdisjoint(bitReports)
audits.update(bitReports)
records.append(('TransferScalarPowBitInteger01',bitTarget['source'],bitResult['objects'][0]))
inputs += bitPool['input_records']+[pin(bits/n) for n in ['prepare_recipe.py','prepare.py','plan.json','events.jsonl','execute_bounded.py','source-mapping.json','handwritten/TransferScalarPowBitInteger01.lean','project/ShielddSecurity/TransferScalarPowBitInteger01.lean']]+[pin(bitStdout),pin(bitPlan['owned_import_pool']['path'])]
assert len(records)==204 and len(audits)==1428
"""
s=s[:start]+merge+s[end:]
replace("'objects': 202","'objects': 204")
start=s.index("composition['field_foundation']");end=s.index("composition_file = POOL / 'composition-review.json'",start)
s=s[:start]+"composition['field_foundation']=old_pool['field_foundation']\ncomposition['shared_word_branch']={'original_math_modules':203,'original_math_reports':1422,'bit_branch_modules':163,'bit_branch_reports':1296,'shared_modules':162,'shared_reports':1290,'all_shared_source_object_and_complete_reports_identical':True,'scope':'Every shared original record reused once, no proof replay or duplicate qualification.'}\ncomposition['scope']='Complete204-module first owned root and1428 complete original reports: whole203-module inverse/prime foundation and whole163-module bit-integer branch with exact shared162-module source/object/report closure verified once. No ancestors replayed.'\n"+s[end:]
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Actual modeled constant/variable square/multiply bit steps and symbolic source word folds derive exact mathematical field powers for complete source pow/pow_vartime, using derived source ONE initial value and exact reconstructed little-endian exponent integer. Six theorem audits. Whole203-module inverse/prime branch and whole163-module bit branch merged with exact shared162-module source/object/report identity; no ancestor replay. Native Choice/library/compiler/ABI/caller/full Transfer remain open.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_inverse_correctness_source_shape']=pin(ROOT/'context/scalar-inverse-correctness-shape.json')","mapping['scalar_inverse_correctness_source_shape']=pin(DIAG/'transfer-scalar-inverse-correctness-20261012-04/context/scalar-inverse-correctness-shape.json')\nmapping['scalar_pow_bit_integer_source_shape']=pin(bits/'context/scalar-pow-bit-integer-shape.json')\nmapping['scalar_pow_field_source_shape']=pin(ROOT/'context/scalar-pow-field-shape.json')")
replace("plan['pins'].append(mapping['scalar_inverse_correctness_source_shape'])","plan['pins'].append(mapping['scalar_inverse_correctness_source_shape'])\nplan['pins'].append(mapping['scalar_pow_bit_integer_source_shape'])\nplan['pins'].append(mapping['scalar_pow_field_source_shape'])")
replace("pin(ROOT/'prepare_recipe_from01.py')","pin(DIAG/'transfer-scalar-inverse-correctness-20261012-04/prepare_recipe_from01.py')")
old='One source and bounded reports/object; complete202-module owned root: original162-module word closure plus qualified40-module prime-tree branch, with the unchanged original qualified Mathlib/core floor.'
new='One source and bounded reports/object; complete204-module owned root with exact shared word foundation and qualified prime/bit branches, and unchanged original qualified Mathlib/core floor.'
replace(old,new)
s=s.replace('SCALAR_INVERSE_CORRECTNESS_COMPLETE_TWO_HUNDRED_TWO_MODULE','SCALAR_POW_FIELD_COMPLETE_TWO_HUNDRED_FOUR_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':1428,'whole_owned_modules':204,'shared_modules_reused_once':162})
