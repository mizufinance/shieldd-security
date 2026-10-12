from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();start=text.index('    pub fn invert(');end=text.index('\n    }',start)+6
body=text[start:end];assert 'square_assign_multi' in body and 'CtOption::new(t0, !self.ct_eq(&Self::zero()))' in body
(ROOT/'context').mkdir()
(ROOT/'context/scalar-invert-machine-shape.json').write_text(json.dumps({'library':pin(library),'invert_body':body,'scope':'Exact cached source repeated-square and multiplication register addition chain, ending CtOption zero refusal. Current proof is generic initialized-read symbolic machine and actual modeled word operations; exact instruction instance/native Choice/compiler/caller/inverse semantics separate.'},indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-pow-invariant-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-square-product-20261011-02'","UPSTREAM = DIAG / 'transfer-scalar-pow-invariant-20261011-01'"),
 ("POOL = DIAG / 'transfer-scalar-pow-invariant-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-invert-machine-owned-floor-20261011-01'"),
 ("MODULE = 'TransferScalarPowInvariant01'","MODULE = 'TransferScalarInvertMachine01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarSquareProduct01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarPowInvariant01/stdout.txt'"),
 ('assert len(current) == 5','assert len(current) == 15'),
 ("records.append(('TransferScalarSquareProduct01'","records.append(('TransferScalarPowInvariant01'"),
 ("'handwritten/TransferScalarSquareProduct01.lean', 'project/ShielddSecurity/TransferScalarSquareProduct01.lean'","'handwritten/TransferScalarPowInvariant01.lean', 'project/ShielddSecurity/TransferScalarPowInvariant01.lean'"),
 ('assert len(names) == 15','assert len(names) == 20'),
 ("'imports': ['ShielddSecurity.TransferScalarSquareProduct01']","'imports': ['ShielddSecurity.TransferScalarPowInvariant01']")]:replace(a,b)
s=s.replace('== 155','== 156').replace('== 1222','== 1237').replace("'objects': 155","'objects': 156").replace('one-hundred-fifty-five-module','one-hundred-fifty-six-module').replace('1222 inherited','1237 inherited').replace("'inherited_audits': 1222","'inherited_audits': 1237")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Small symbolic inversion register machine refuses uninitialized operands, uses proved actual modeled multiplication and symbolic repeated optimized squares, and proves initialized source reads yield successful canonical updated registers throughout a well-formed walk. Parallel optional natural-exponent machine supports an exact finite source chain certificate; it alone does not prove field exponent semantics. Two inductives/fourteen definitions/four theorems. Exact parsed source instruction instance/zero choice, mathematical inverse and native Choice/library/compiler/ABI/caller/full Transfer OPEN; no native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_pow_invariant_source_shape']=pin(ROOT/'context/scalar-pow-invariant-shape.json')","mapping['scalar_pow_invariant_source_shape']=pin(DIAG/'transfer-scalar-pow-invariant-20261011-01/context/scalar-pow-invariant-shape.json')\nmapping['scalar_invert_machine_source_shape']=pin(ROOT/'context/scalar-invert-machine-shape.json')")
replace("plan['pins'].append(mapping['scalar_pow_invariant_source_shape'])","plan['pins'].append(mapping['scalar_pow_invariant_source_shape'])\nplan['pins'].append(mapping['scalar_invert_machine_source_shape'])")
s=s.replace("'fresh_audits': 15","'fresh_audits': 20").replace('SCALAR_POW_INVARIANT_COMPLETE_ONE_HUNDRED_FIFTY_FIVE_MODULE','SCALAR_INVERT_MACHINE_COMPLETE_ONE_HUNDRED_FIFTY_SIX_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':20,'inherited_reports':1237,'owned_modules':156})
