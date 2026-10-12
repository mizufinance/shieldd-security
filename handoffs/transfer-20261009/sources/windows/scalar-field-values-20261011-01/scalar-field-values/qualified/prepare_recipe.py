from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
upstream=DIAG/'transfer-scalar-extended-family-20261012-01'
events=[json.loads(line) for line in (upstream/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='passed'
(ROOT/'context').mkdir()
(ROOT/'context/scalar-field-values-shape.json').write_text(json.dumps({
 'scope':'Exact mathematical field values follow from already proved actual modeled canonical multiplication and optimized square Montgomery contracts plus exact radix inverse. Repeated-square power follows by a symbolic count induction. Four theorem audits; no new word algorithm or assumed desired equation. Native/compiler/caller and full Transfer remain open.',
 'source_contracts':[pin(DIAG/'transfer-scalar-wide-reduction-20261011-02/handwritten/TransferScalarWideReduction01.lean'),pin(DIAG/'transfer-scalar-square-product-20261011-02/handwritten/TransferScalarSquareProduct01.lean'),pin(DIAG/'transfer-scalar-pow-invariant-20261011-01/handwritten/TransferScalarPowInvariant01.lean')]
},indent=2,sort_keys=True)+'\n')
s=(upstream/'prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-public-constants-20261011-02'","UPSTREAM = DIAG / 'transfer-scalar-extended-family-20261012-01'"),
 ("POOL = DIAG / 'transfer-scalar-extended-family-owned-floor-20261012-01'","POOL = DIAG / 'transfer-scalar-field-values-owned-floor-20261012-01'"),
 ("MODULE = 'TransferScalarExtendedFamily01'","MODULE = 'TransferScalarFieldValues01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarPublicConstants01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarExtendedFamily01/stdout.txt'"),
 ('assert len(current) == 6','assert len(current) == 4'),
 ("records.append(('TransferScalarPublicConstants01'","records.append(('TransferScalarExtendedFamily01'"),
 ("'handwritten/TransferScalarPublicConstants01.lean', 'project/ShielddSecurity/TransferScalarPublicConstants01.lean'","'handwritten/TransferScalarExtendedFamily01.lean', 'project/ShielddSecurity/TransferScalarExtendedFamily01.lean'"),
 ("'imports': ['ShielddSecurity.TransferScalarPublicConstants01']","'imports': ['ShielddSecurity.TransferScalarExtendedFamily01']")]:replace(a,b)
s=s.replace('== 159','== 160').replace('== 1275','== 1279').replace("'objects': 159","'objects': 160").replace('one-hundred-fifty-nine-module','one-hundred-sixty-module').replace('1275 inherited','1279 inherited').replace("'inherited_audits': 1275","'inherited_audits': 1279")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Derived mathematical Montgomery field values of actual modeled canonical multiplication/optimized square and symbolic repeated-square power, using exact radix inverse and modular algebra. Four theorem audits. Native library/compiler/ABI/caller, field inverse and full Transfer remain open.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_extended_family_source_shape']=pin(ROOT/'context/scalar-extended-family-shape.json')","mapping['scalar_extended_family_source_shape']=pin(DIAG/'transfer-scalar-extended-family-20261012-01/context/scalar-extended-family-shape.json')\nmapping['scalar_field_values_source_shape']=pin(ROOT/'context/scalar-field-values-shape.json')")
replace("plan['pins'].append(mapping['scalar_extended_family_source_shape'])","plan['pins'].append(mapping['scalar_extended_family_source_shape'])\nplan['pins'].append(mapping['scalar_field_values_source_shape'])")
s=s.replace('SCALAR_EXTENDED_FAMILY_COMPLETE_ONE_HUNDRED_FIFTY_NINE_MODULE','SCALAR_FIELD_VALUES_COMPLETE_ONE_HUNDRED_SIXTY_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':1279,'owned_modules':160})
