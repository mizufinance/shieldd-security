from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();start=text.index('    pub const fn square(');end=text.index('\n    }',start)+6
body=text[start:end];assert body.count('mac(')==10 and body.count('adc(')==4 and body.count('montgomery_reduce(')==1
(ROOT/'context').mkdir()
(ROOT/'context/scalar-square-product-shape.json').write_text(json.dumps({'library':pin(library),'square_body':body,'scope':'Exact cached source optimized square six cross MACs, adjacent doubling shifts, four diagonal MAC/ADC pairs, ignored final carry and eight-argument Montgomery reduction. Arithmetic model join; native source/compiler/caller correspondence separate.'},indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-square-diagonal-20261011-04/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-square-shift-20261011-04'","UPSTREAM = DIAG / 'transfer-scalar-square-diagonal-20261011-04'"),
 ("POOL = DIAG / 'transfer-scalar-square-diagonal-owned-floor-20261011-04'","POOL = DIAG / 'transfer-scalar-square-product-owned-floor-20261011-01'"),
 ("MODULE = 'TransferScalarSquareDiagonal01'","MODULE = 'TransferScalarSquareProduct01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarSquareShift01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarSquareDiagonal01/stdout.txt'"),
 ('assert len(current) == 7','assert len(current) == 4'),
 ("records.append(('TransferScalarSquareShift01'","records.append(('TransferScalarSquareDiagonal01'"),
 ("'handwritten/TransferScalarSquareShift01.lean', 'project/ShielddSecurity/TransferScalarSquareShift01.lean'","'handwritten/TransferScalarSquareDiagonal01.lean', 'project/ShielddSecurity/TransferScalarSquareDiagonal01.lean'"),
 ('assert len(names) == 4','assert len(names) == 5'),
 ("'imports': ['ShielddSecurity.TransferScalarSquareShift01']","'imports': ['ShielddSecurity.TransferScalarSquareDiagonal01']")]:replace(a,b)
s=s.replace('== 153','== 154').replace('== 1213','== 1217').replace("'objects': 153","'objects': 154").replace('one-hundred-fifty-three-module','one-hundred-fifty-four-module').replace('1213 inherited','1217 inherited').replace("'inherited_audits': 1213","'inherited_audits': 1217")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Actual modeled optimized source square joins six cross MACs, seven shifts, four diagonal MAC/ADC pairs and exact eight-word Montgomery reduction. Exact full square integer and eight-word raw bound derive zero ignored final ADC carry. Canonical input derives width4/canonical output and exact Montgomery square relation without caller desired carry/value/range premise. Two definitions/three theorems. Pow/invert and native primitive/library/compiler/ABI/caller correspondence/full Transfer OPEN; no native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_square_diagonal_source_shape']=pin(ROOT/'context/scalar-square-diagonal-shape.json')","mapping['scalar_square_diagonal_source_shape']=pin(DIAG/'transfer-scalar-square-diagonal-20261011-04/context/scalar-square-diagonal-shape.json')\nmapping['scalar_square_product_source_shape']=pin(ROOT/'context/scalar-square-product-shape.json')")
replace("plan['pins'].append(mapping['scalar_square_diagonal_source_shape'])","plan['pins'].append(mapping['scalar_square_diagonal_source_shape'])\nplan['pins'].append(mapping['scalar_square_product_source_shape'])")
s=s.replace("'fresh_audits': 4","'fresh_audits': 5").replace('SCALAR_SQUARE_DIAGONAL_COMPLETE_ONE_HUNDRED_FIFTY_THREE_MODULE','SCALAR_SQUARE_PRODUCT_COMPLETE_ONE_HUNDRED_FIFTY_FOUR_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':5,'inherited_reports':1217,'owned_modules':154})
