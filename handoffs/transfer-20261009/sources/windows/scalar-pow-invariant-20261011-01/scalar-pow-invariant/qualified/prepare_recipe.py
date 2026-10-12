from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text()
def body(marker):
    start=text.index(marker);end=text.index('\n    }',start)+6
    return text[start:end]
powBody=body('    pub fn pow(');varBody=body('    pub fn pow_vartime(');invBody=body('    pub fn invert(')
assert powBody.count('.rev()')==2 and varBody.count('.rev()')==2 and 'res.conditional_assign' in powBody
(ROOT/'context').mkdir()
(ROOT/'context/scalar-pow-invariant-shape.json').write_text(json.dumps({'library':pin(library),'source_zero':body('    pub const fn zero('),'source_one':body('    pub const fn one('),'R_constant':text[text.index('const R: Scalar'):text.index(';',text.index('const R: Scalar'))+1],'pow_body':powBody,'pow_vartime_body':varBody,'invert_square_assign_helper':invBody[:invBody.index('        // found')],'scope':'Exact cached zero/ONE/R constant, reverse four-word/64-bit pow and pow_vartime loop bodies and repeated-square helper. Arithmetic canonical result and branch-selection model; native Choice/conditional assignment, compiler/caller and mathematical exponent semantics separate.'},indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-square-product-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-square-diagonal-20261011-04'","UPSTREAM = DIAG / 'transfer-scalar-square-product-20261011-02'"),
 ("POOL = DIAG / 'transfer-scalar-square-product-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-pow-invariant-owned-floor-20261011-01'"),
 ("MODULE = 'TransferScalarSquareProduct01'","MODULE = 'TransferScalarPowInvariant01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarSquareDiagonal01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarSquareProduct01/stdout.txt'"),
 ('assert len(current) == 4','assert len(current) == 5'),
 ("records.append(('TransferScalarSquareDiagonal01'","records.append(('TransferScalarSquareProduct01'"),
 ("'handwritten/TransferScalarSquareDiagonal01.lean', 'project/ShielddSecurity/TransferScalarSquareDiagonal01.lean'","'handwritten/TransferScalarSquareProduct01.lean', 'project/ShielddSecurity/TransferScalarSquareProduct01.lean'"),
 ('assert len(names) == 5','assert len(names) == 15'),
 ("'imports': ['ShielddSecurity.TransferScalarSquareDiagonal01']","'imports': ['ShielddSecurity.TransferScalarSquareProduct01']")]:replace(a,b)
s=s.replace('== 154','== 155').replace('== 1217','== 1222').replace("'objects': 154","'objects': 155").replace('one-hundred-fifty-four-module','one-hundred-fifty-five-module').replace('1217 inherited','1222 inherited').replace("'inherited_audits': 1217","'inherited_audits': 1222")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Source ZERO/ONE exact canonical Montgomery keys and proved actual modeled multiply/optimized square outputs derive canonical constant-time and variable-time pow step/loop results and repeated-square results. Reverse four-word/64-bit loops use UInt64 shift/AND equality bit selection; modeled returned fields agree. Eleven definitions/four theorems. Mathematical exponent/inverse semantics, native Choice/conditional assignment/library/compiler/ABI/caller/full Transfer OPEN; no native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_square_product_source_shape']=pin(ROOT/'context/scalar-square-product-shape.json')","mapping['scalar_square_product_source_shape']=pin(DIAG/'transfer-scalar-square-product-20261011-02/context/scalar-square-product-shape.json')\nmapping['scalar_pow_invariant_source_shape']=pin(ROOT/'context/scalar-pow-invariant-shape.json')")
replace("plan['pins'].append(mapping['scalar_square_product_source_shape'])","plan['pins'].append(mapping['scalar_square_product_source_shape'])\nplan['pins'].append(mapping['scalar_pow_invariant_source_shape'])")
s=s.replace("'fresh_audits': 5","'fresh_audits': 15").replace('SCALAR_SQUARE_PRODUCT_COMPLETE_ONE_HUNDRED_FIFTY_FOUR_MODULE','SCALAR_POW_INVARIANT_COMPLETE_ONE_HUNDRED_FIFTY_FIVE_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':15,'inherited_reports':1222,'owned_modules':155})
