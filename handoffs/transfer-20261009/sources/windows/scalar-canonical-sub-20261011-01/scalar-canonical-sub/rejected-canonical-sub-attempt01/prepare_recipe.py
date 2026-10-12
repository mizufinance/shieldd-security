from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
context=ROOT/'context';context.mkdir()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();start=text.index('    pub const fn sub(');end=text.index('    ///',start+1)
body=text[start:end];assert body.count('sbb(')==4 and body.count('adc(')==4 and body.count('& borrow')==4
shape={'library':pin(library),'source_sub_body':body,'scope':'Exact authenticated cached Scalar sub source four SBB then four borrow-masked ADC, discarded final carry. Static identity/arithmetic model only; native Rust primitive/compiler/private Scalar/caller correspondence separate.'}
(context/'scalar-canonical-sub-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-canonical-add-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-checked-word-accepted-input-20261011-02'","UPSTREAM = DIAG / 'transfer-scalar-canonical-add-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-canonical-add-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-canonical-sub-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarCanonicalAdd01'","MODULE = 'TransferScalarCanonicalSub01'")
replace("stdout = UPSTREAM / 'runs/01-TransferCheckedWordAcceptedInput01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarCanonicalAdd01/stdout.txt'")
replace('assert len(current) == 4','assert len(current) == 5')
replace("records.append(('TransferCheckedWordAcceptedInput01'","records.append(('TransferScalarCanonicalAdd01'")
replace("'handwritten/TransferCheckedWordAcceptedInput01.lean', 'project/ShielddSecurity/TransferCheckedWordAcceptedInput01.lean'","'handwritten/TransferScalarCanonicalAdd01.lean', 'project/ShielddSecurity/TransferScalarCanonicalAdd01.lean'")
s=s.replace('== 144','== 145').replace('== 1167','== 1172').replace("'objects': 144","'objects': 145").replace('one-hundred-forty-four-module','one-hundred-forty-five-module').replace('1167 inherited','1172 inherited').replace("'inherited_audits': 1167","'inherited_audits': 1172")
replace('assert len(names) == 5','assert len(names) == 3')
replace("'imports': ['ShielddSecurity.TransferCheckedWordAcceptedInput01']","'imports': ['ShielddSecurity.TransferScalarCanonicalAdd01']")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Actual Scalar.sub four SBB recurrence then four borrow-masked ADC derives four output limbs and canonical exact modular subtraction from canonical raw operands. One definition/two theorem audits. Another private Scalar operation model; global constructor/other operation/private representation invariant and native Rust primitive/compiler/ABI/caller correspondence remain OPEN. No native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_canonical_add_source_shape']=pin(ROOT/'context/scalar-canonical-add-shape.json')","mapping['scalar_canonical_add_source_shape']=pin(DIAG/'transfer-scalar-canonical-add-20261011-02/context/scalar-canonical-add-shape.json')\nmapping['scalar_canonical_sub_source_shape']=pin(ROOT/'context/scalar-canonical-sub-shape.json')")
replace("plan['pins'].append(mapping['scalar_canonical_add_source_shape'])","plan['pins'].append(mapping['scalar_canonical_add_source_shape'])\nplan['pins'].append(mapping['scalar_canonical_sub_source_shape'])")
s=s.replace("'fresh_audits': 5","'fresh_audits': 3").replace('SCALAR_CANONICAL_ADD_COMPLETE_ONE_HUNDRED_FORTY_FOUR_MODULE','SCALAR_CANONICAL_SUB_COMPLETE_ONE_HUNDRED_FORTY_FIVE_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':3,'inherited_reports':1172,'owned_modules':145,'source_shape':pin(context/'scalar-canonical-sub-shape.json')})
