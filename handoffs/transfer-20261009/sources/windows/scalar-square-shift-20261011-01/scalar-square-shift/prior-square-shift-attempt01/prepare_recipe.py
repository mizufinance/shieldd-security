from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();start=text.index('    pub const fn square(');end=text.index('\n    }',start)+6
body=text[start:end];shifts=body[body.index('        let r7 ='):body.index('        // Add')]
assert shifts.count('<< 1')==6 and shifts.count('>> 63')==6
(ROOT/'context').mkdir()
(ROOT/'context/scalar-square-shift-shape.json').write_text(json.dumps({'library':pin(library),'square_body':body,'shift_assignments':shifts,'scope':'Exact cached source shifts for cross terms. Static association only; diagonal/reduction/native/compiler/caller remain separate.'},indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-square-cross-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-input-family-20261011-04'","UPSTREAM = DIAG / 'transfer-scalar-square-cross-20261011-02'"),
 ("POOL = DIAG / 'transfer-scalar-square-cross-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-square-shift-owned-floor-20261011-01'"),
 ("MODULE = 'TransferScalarSquareCross01'","MODULE = 'TransferScalarSquareShift01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarInputFamily01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarSquareCross01/stdout.txt'"),
 ('assert len(current) == 5','assert len(current) == 6'),
 ("records.append(('TransferScalarInputFamily01'","records.append(('TransferScalarSquareCross01'"),
 ("'handwritten/TransferScalarInputFamily01.lean', 'project/ShielddSecurity/TransferScalarInputFamily01.lean'","'handwritten/TransferScalarSquareCross01.lean', 'project/ShielddSecurity/TransferScalarSquareCross01.lean'"),
 ('assert len(names) == 6','assert len(names) == 7'),
 ("'imports': ['ShielddSecurity.TransferScalarInputFamily01']","'imports': ['ShielddSecurity.TransferScalarSquareCross01']")]:replace(a,b)
s=s.replace('== 151','== 152').replace('== 1200','== 1206').replace("'objects': 151","'objects': 152").replace('one-hundred-fifty-one-module','one-hundred-fifty-two-module').replace('1200 inherited','1206 inherited').replace("'inherited_audits': 1200","'inherited_audits': 1206")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Actual modeled source adjacent UInt64 shifts/OR derive disjoint low-bit sum and conserve doubled word plus top bit. Symbolic recurrence derives exact doubled seven-word cross value and eight-word output. Two definitions/five theorems. Diagonal terms/reduction/native primitives/library/compiler/ABI/caller correspondence and full Transfer OPEN; no native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_square_cross_source_shape']=pin(ROOT/'context/scalar-square-cross-shape.json')","mapping['scalar_square_cross_source_shape']=pin(DIAG/'transfer-scalar-square-cross-20261011-02/context/scalar-square-cross-shape.json')\nmapping['scalar_square_shift_source_shape']=pin(ROOT/'context/scalar-square-shift-shape.json')")
replace("plan['pins'].append(mapping['scalar_square_cross_source_shape'])","plan['pins'].append(mapping['scalar_square_cross_source_shape'])\nplan['pins'].append(mapping['scalar_square_shift_source_shape'])")
s=s.replace("'fresh_audits': 6","'fresh_audits': 7").replace('SCALAR_SQUARE_CROSS_COMPLETE_ONE_HUNDRED_FIFTY_ONE_MODULE','SCALAR_SQUARE_SHIFT_COMPLETE_ONE_HUNDRED_FIFTY_TWO_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':1206,'owned_modules':152})
