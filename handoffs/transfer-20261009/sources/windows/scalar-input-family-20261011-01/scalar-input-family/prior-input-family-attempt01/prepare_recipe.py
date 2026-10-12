from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
context=ROOT/'context';context.mkdir()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();start=text.index('    pub fn from_bytes(');end=text.index('\n    }',start)+6
body=text[start:end];assert 'CtOption::new(tmp, Choice::from(is_some))' in body and 'tmp *= &R2' in body
shape={'library':pin(library),'from_bytes_body':body,'represented_constructors':['arbitrary four raw words via R2','arbitrary64 bytes via R2/R3','canonical32 byte Choice success projection'],'represented_operations':['add','sub','mul','neg','double'],'excluded':['square','pow','invert','random','arbitrary private constructors'],'scope':'Extended represented source input family, no caller canonical operand bound. Actual modeled32-byte Choice success/refusal projection retained; native CtOption/Choice/program/caller/private Scalar/primitive/compiler/ABI binding OPEN.'}
(context/'scalar-input-family-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-wide-byte-input-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-wide-constructor-20261011-03'","UPSTREAM = DIAG / 'transfer-scalar-wide-byte-input-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-wide-byte-input-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-input-family-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarWideByteInput01'","MODULE = 'TransferScalarInputFamily01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarWideConstructor01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarWideByteInput01/stdout.txt'")
replace('assert len(current) == 6','assert len(current) == 4')
replace("records.append(('TransferScalarWideConstructor01'","records.append(('TransferScalarWideByteInput01'")
replace("'handwritten/TransferScalarWideConstructor01.lean', 'project/ShielddSecurity/TransferScalarWideConstructor01.lean'","'handwritten/TransferScalarWideByteInput01.lean', 'project/ShielddSecurity/TransferScalarWideByteInput01.lean'")
s=s.replace('== 149','== 150').replace('== 1191','== 1195').replace("'objects': 149","'objects': 150").replace('one-hundred-forty-nine-module','one-hundred-fifty-module').replace('1191 inherited','1195 inherited').replace("'inherited_audits': 1191","'inherited_audits': 1195")
replace('assert len(names) == 4','assert len(names) == 5')
replace("'imports': ['ShielddSecurity.TransferScalarWideConstructor01']","'imports': ['ShielddSecurity.TransferScalarWideByteInput01']")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Extended represented source family accepts arbitrary raw4 words, wide64 bytes, and32-byte canonical Choice success projection, then modeled add/sub/mul/neg/double. Constructor refusal propagates; every returned eval output derives canonical raw field/32-byte exact Montgomery key from proved constructor/operation contracts with no caller invariant. Actual modeled32-byte decoder success/refusal projection retained and returned constructor reserializes exact original bytes. One inductive/one definition/three theorem audits. Excludes square/pow/invert/random/private constructors; native program/Choice/CtOption/caller/private Scalar/primitive/compiler/ABI correspondence OPEN. No native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_wide_byte_input_source_shape']=pin(ROOT/'context/scalar-wide-byte-input-shape.json')","mapping['scalar_wide_byte_input_source_shape']=pin(DIAG/'transfer-scalar-wide-byte-input-20261011-02/context/scalar-wide-byte-input-shape.json')\nmapping['scalar_input_family_source_shape']=pin(ROOT/'context/scalar-input-family-shape.json')")
replace("plan['pins'].append(mapping['scalar_wide_byte_input_source_shape'])","plan['pins'].append(mapping['scalar_wide_byte_input_source_shape'])\nplan['pins'].append(mapping['scalar_input_family_source_shape'])")
s=s.replace("'fresh_audits': 4","'fresh_audits': 5").replace('SCALAR_WIDE_BYTE_INPUT_COMPLETE_ONE_HUNDRED_FORTY_NINE_MODULE','SCALAR_INPUT_FAMILY_COMPLETE_ONE_HUNDRED_FIFTY_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':5,'inherited_reports':1195,'owned_modules':150,'source_shape':pin(context/'scalar-input-family-shape.json')})
