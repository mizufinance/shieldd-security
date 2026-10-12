from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
upstream=DIAG/'transfer-scalar-field-values-20261012-01'
events=[json.loads(line) for line in (upstream/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='passed'
(ROOT/'context').mkdir()
(ROOT/'context/scalar-invert-field-shape.json').write_text(json.dumps({
 'scope':'Symbolic simulation of the actual modeled Montgomery inversion register walk by its parallel natural-exponent walk. Operand reads, register updates, square/multiply steps and instruction-list induction derive the field exponent. The independently checked exact cached source85-statement natural certificate supplies modulus minus two. No conclusion-shaped field exponent premise. Primality/Fermat and native compiler/caller binding remain separate.',
 'source_machine':pin(DIAG/'transfer-scalar-invert-machine-20261011-01/handwritten/TransferScalarInvertMachine01.lean'),
 'source_instance':pin(DIAG/'transfer-scalar-invert-chain-20261011-05/generated/TransferScalarInvertChain01.lean'),
 'mathematical_operations':pin(upstream/'handwritten/TransferScalarFieldValues01.lean')
},indent=2,sort_keys=True)+'\n')
s=(upstream/'prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-extended-family-20261012-01'","UPSTREAM = DIAG / 'transfer-scalar-field-values-20261012-01'"),
 ("POOL = DIAG / 'transfer-scalar-field-values-owned-floor-20261012-01'","POOL = DIAG / 'transfer-scalar-invert-field-owned-floor-20261012-01'"),
 ("MODULE = 'TransferScalarFieldValues01'","MODULE = 'TransferScalarInvertField01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarExtendedFamily01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarFieldValues01/stdout.txt'"),
 ("records.append(('TransferScalarExtendedFamily01'","records.append(('TransferScalarFieldValues01'"),
 ("'handwritten/TransferScalarExtendedFamily01.lean', 'project/ShielddSecurity/TransferScalarExtendedFamily01.lean'","'handwritten/TransferScalarFieldValues01.lean', 'project/ShielddSecurity/TransferScalarFieldValues01.lean'"),
 ('assert len(names) == 4','assert len(names) == 7'),
 ("'imports': ['ShielddSecurity.TransferScalarExtendedFamily01']","'imports': ['ShielddSecurity.TransferScalarFieldValues01']")]:replace(a,b)
s=s.replace('== 160','== 161').replace('== 1279','== 1283').replace("'objects': 160","'objects': 161").replace('one-hundred-sixty-module','one-hundred-sixty-one-module').replace('1279 inherited','1283 inherited').replace("'inherited_audits': 1279","'inherited_audits': 1283")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Symbolic actual modeled Montgomery inversion register machine/parallel natural-exponent simulation, deriving every successful source payload field value as input^(p-2) modulo p from exact independently checked source85-statement certificate. One definition/six theorems. Field inverse via primality/Fermat and native library/compiler/ABI/caller/full Transfer remain open.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_field_values_source_shape']=pin(ROOT/'context/scalar-field-values-shape.json')","mapping['scalar_field_values_source_shape']=pin(DIAG/'transfer-scalar-field-values-20261012-01/context/scalar-field-values-shape.json')\nmapping['scalar_invert_field_source_shape']=pin(ROOT/'context/scalar-invert-field-shape.json')")
replace("plan['pins'].append(mapping['scalar_field_values_source_shape'])","plan['pins'].append(mapping['scalar_field_values_source_shape'])\nplan['pins'].append(mapping['scalar_invert_field_source_shape'])")
s=s.replace("'fresh_audits': 4","'fresh_audits': 7").replace('SCALAR_FIELD_VALUES_COMPLETE_ONE_HUNDRED_SIXTY_MODULE','SCALAR_INVERT_FIELD_COMPLETE_ONE_HUNDRED_SIXTY_ONE_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':1283,'owned_modules':161})
