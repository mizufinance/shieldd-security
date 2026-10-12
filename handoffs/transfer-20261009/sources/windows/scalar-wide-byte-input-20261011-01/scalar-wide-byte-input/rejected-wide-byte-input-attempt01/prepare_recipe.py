from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
context=ROOT/'context';context.mkdir()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();start=text.index('    pub fn from_bytes_wide(');end=text.index('\n    }',start)+6
body=text[start:end];assert body.count('u64::from_le_bytes')==8 and all('bytes['+str(i*8)+'..'+str((i+1)*8)+']' in body for i in range(8))
shape={'library':pin(library),'from_bytes_wide_body':body,'scope':'Exact authenticated cached eight ordered8-byte LE read slices and from_u512 call. Arithmetic model typed64-byte input derives low/high digits and whole integer; native from_le_bytes/slice/array/index/private Scalar/primitive/compiler/caller bindings separate.'}
(context/'scalar-wide-byte-input-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-wide-constructor-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-program-invariant-20261011-01'","UPSTREAM = DIAG / 'transfer-scalar-wide-constructor-20261011-03'")
replace("POOL = DIAG / 'transfer-scalar-wide-constructor-owned-floor-20261011-03'","POOL = DIAG / 'transfer-scalar-wide-byte-input-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarWideConstructor01'","MODULE = 'TransferScalarWideByteInput01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarProgramInvariant01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarWideConstructor01/stdout.txt'")
replace('assert len(current) == 4','assert len(current) == 6')
replace("records.append(('TransferScalarProgramInvariant01'","records.append(('TransferScalarWideConstructor01'")
replace("'handwritten/TransferScalarProgramInvariant01.lean', 'project/ShielddSecurity/TransferScalarProgramInvariant01.lean'","'handwritten/TransferScalarWideConstructor01.lean', 'project/ShielddSecurity/TransferScalarWideConstructor01.lean'")
s=s.replace('== 148','== 149').replace('== 1185','== 1191').replace("'objects': 148","'objects': 149").replace('one-hundred-forty-eight-module','one-hundred-forty-nine-module').replace('1185 inherited','1191 inherited').replace("'inherited_audits': 1185","'inherited_audits': 1191")
replace('assert len(names) == 6','assert len(names) == 4')
replace("'imports': ['ShielddSecurity.TransferScalarProgramInvariant01']","'imports': ['ShielddSecurity.TransferScalarWideConstructor01']")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Actual modeled from_bytes_wide arbitrary typed64-byte input derives eight consecutive eight-byte LE reads, exact low/high four-word digit reconstruction and full512-bit integer. Joined source from_u512 R2/R3 mul/add model derives canonical payload, exact key=original64-byte integer modulo p and32-byte output. Two definitions/two theorem audits; no caller input canonical bound or desired digits/payload/key. Native byte/slice/array/index/private Scalar/primitive/compiler/ABI/caller correspondence OPEN. No native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_wide_constructor_source_shape']=pin(ROOT/'context/scalar-wide-constructor-shape.json')","mapping['scalar_wide_constructor_source_shape']=pin(DIAG/'transfer-scalar-wide-constructor-20261011-03/context/scalar-wide-constructor-shape.json')\nmapping['scalar_wide_byte_input_source_shape']=pin(ROOT/'context/scalar-wide-byte-input-shape.json')")
replace("plan['pins'].append(mapping['scalar_wide_constructor_source_shape'])","plan['pins'].append(mapping['scalar_wide_constructor_source_shape'])\nplan['pins'].append(mapping['scalar_wide_byte_input_source_shape'])")
s=s.replace("'fresh_audits': 6","'fresh_audits': 4").replace('SCALAR_WIDE_CONSTRUCTOR_COMPLETE_ONE_HUNDRED_FORTY_EIGHT_MODULE','SCALAR_WIDE_BYTE_INPUT_COMPLETE_ONE_HUNDRED_FORTY_NINE_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':1191,'owned_modules':149,'source_shape':pin(context/'scalar-wide-byte-input-shape.json')})
