from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
upstream=DIAG/'transfer-scalar-invert-field-20261012-03'
events=[json.loads(line) for line in (upstream/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='passed'
(ROOT/'context').mkdir()
(ROOT/'context/scalar-pow-bit-integer-shape.json').write_text(json.dumps({
 'scope':'Exact modeled UInt64 shift-right/ofNat/mask/Boolean comparison and bounded source index yield natural binary digit. Symbolic count recurrence and member-step/list recurrence derive exact64-bit word and arbitrary reversed-word little-endian exponent integer; no unrolled wide walk. Native/compiler/caller binding and mathematical field-power fold are separate.',
 'source_power_model':pin(DIAG/'transfer-scalar-pow-invariant-20261011-01/handwritten/TransferScalarPowInvariant01.lean'),
 'official_uint_bitwise_source':pin(Path('C:/Users/acyrn/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Data/UInt/Bitwise.lean')),
 'official_nat_modular_source':pin(Path('C:/Users/acyrn/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Data/Nat/Mod.lean'))
},indent=2,sort_keys=True)+'\n')
s=(upstream/'prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-field-values-20261012-01'","UPSTREAM = DIAG / 'transfer-scalar-invert-field-20261012-03'"),
 ("POOL = DIAG / 'transfer-scalar-invert-field-owned-floor-20261012-03'","POOL = DIAG / 'transfer-scalar-pow-bit-integer-owned-floor-20261012-01'"),
 ("MODULE = 'TransferScalarInvertField01'","MODULE = 'TransferScalarPowBitInteger01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarFieldValues01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarInvertField01/stdout.txt'"),
 ('assert len(current) == 4','assert len(current) == 7'),
 ("records.append(('TransferScalarFieldValues01'","records.append(('TransferScalarInvertField01'"),
 ("'handwritten/TransferScalarFieldValues01.lean', 'project/ShielddSecurity/TransferScalarFieldValues01.lean'","'handwritten/TransferScalarInvertField01.lean', 'project/ShielddSecurity/TransferScalarInvertField01.lean'"),
 ('assert len(names) == 7','assert len(names) == 6'),
 ("'imports': ['ShielddSecurity.TransferScalarFieldValues01']","'imports': ['ShielddSecurity.TransferScalarInvertField01']")]:replace(a,b)
s=s.replace('== 161','== 162').replace('== 1283','== 1290').replace("'objects': 161","'objects': 162").replace('one-hundred-sixty-one-module','one-hundred-sixty-two-module').replace('1283 inherited','1290 inherited').replace("'inherited_audits': 1283","'inherited_audits': 1290")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Actual modeled bounded UInt64 shift/mask Boolean bit has exact natural binary digit. Symbolic count/member-step/list recurrences prove every modeled64-bit word loop and reversed word exponent walk reconstructs exact little-endian integer. Six theorem audits; no unrolled256-bit walk. Mathematical field-power fold and native compiler/caller/full Transfer remain open.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_invert_field_source_shape']=pin(ROOT/'context/scalar-invert-field-shape.json')","mapping['scalar_invert_field_source_shape']=pin(DIAG/'transfer-scalar-invert-field-20261012-03/context/scalar-invert-field-shape.json')\nmapping['scalar_pow_bit_integer_source_shape']=pin(ROOT/'context/scalar-pow-bit-integer-shape.json')")
replace("plan['pins'].append(mapping['scalar_invert_field_source_shape'])","plan['pins'].append(mapping['scalar_invert_field_source_shape'])\nplan['pins'].append(mapping['scalar_pow_bit_integer_source_shape'])")
s=s.replace("'fresh_audits': 7","'fresh_audits': 6").replace('SCALAR_INVERT_FIELD_COMPLETE_ONE_HUNDRED_SIXTY_ONE_MODULE','SCALAR_POW_BIT_INTEGER_COMPLETE_ONE_HUNDRED_SIXTY_TWO_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':1290,'owned_modules':162,'inverse_correctness_sibling_not_imported':True})
