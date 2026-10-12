from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
context=ROOT/'context';context.mkdir()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();start=text.index('    pub const fn square(');end=text.index('\n    }',start)+6
body=text[start:end];prefix=body[:body.index('        let r7 =')]
assert prefix.count('mac(')==6 and body.count('mac(')==10 and body.count('adc(')==4
shape={'library':pin(library),'square_body':body,'cross_mac_prefix':prefix,'cross_row_lengths':[3,2,1],'scope':'Exact authenticated cached source square six cross MAC prefix and full remaining shift/diagonal/reduction body. Current arithmetic proof derives only symbolic cross-prefix widths/integer value; shifts/diagonal/final reduction/native primitive/compiler/caller binding separate.'}
(context/'scalar-square-cross-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-input-family-20261011-04/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-wide-byte-input-20261011-02'","UPSTREAM = DIAG / 'transfer-scalar-input-family-20261011-04'")
replace("POOL = DIAG / 'transfer-scalar-input-family-owned-floor-20261011-04'","POOL = DIAG / 'transfer-scalar-square-cross-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarInputFamily01'","MODULE = 'TransferScalarSquareCross01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarWideByteInput01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarInputFamily01/stdout.txt'")
replace('assert len(current) == 4','assert len(current) == 5')
replace("records.append(('TransferScalarWideByteInput01'","records.append(('TransferScalarInputFamily01'")
replace("'handwritten/TransferScalarWideByteInput01.lean', 'project/ShielddSecurity/TransferScalarWideByteInput01.lean'","'handwritten/TransferScalarInputFamily01.lean', 'project/ShielddSecurity/TransferScalarInputFamily01.lean'")
s=s.replace('== 150','== 151').replace('== 1195','== 1200').replace("'objects': 150","'objects': 151").replace('one-hundred-fifty-module','one-hundred-fifty-one-module').replace('1195 inherited','1200 inherited').replace("'inherited_audits': 1195","'inherited_audits': 1200")
replace('assert len(names) == 5','assert len(names) == 6')
replace("'imports': ['ShielddSecurity.TransferScalarWideByteInput01']","'imports': ['ShielddSecurity.TransferScalarInputFamily01']")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Actual modeled source square cross prefix uses six MACs in shrinking3/2/1 rows. Appended carries retain exact full row integer and symbolic crossWalk derives two retained limbs per shrinking row, seven-word source prefix and exact crossValue integer. Three definitions/three theorem audits. No unrolled wide constraints or caller desired carries/values. Square shifts/diagonal/final reduction and native primitive/library/compiler/ABI/caller correspondence OPEN. No native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_input_family_source_shape']=pin(ROOT/'context/scalar-input-family-shape.json')","mapping['scalar_input_family_source_shape']=pin(DIAG/'transfer-scalar-input-family-20261011-04/context/scalar-input-family-shape.json')\nmapping['scalar_square_cross_source_shape']=pin(ROOT/'context/scalar-square-cross-shape.json')")
replace("plan['pins'].append(mapping['scalar_input_family_source_shape'])","plan['pins'].append(mapping['scalar_input_family_source_shape'])\nplan['pins'].append(mapping['scalar_square_cross_source_shape'])")
s=s.replace("'fresh_audits': 5","'fresh_audits': 6").replace('SCALAR_INPUT_FAMILY_COMPLETE_ONE_HUNDRED_FIFTY_MODULE','SCALAR_SQUARE_CROSS_COMPLETE_ONE_HUNDRED_FIFTY_ONE_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':1200,'owned_modules':151,'source_shape':pin(context/'scalar-square-cross-shape.json')})
