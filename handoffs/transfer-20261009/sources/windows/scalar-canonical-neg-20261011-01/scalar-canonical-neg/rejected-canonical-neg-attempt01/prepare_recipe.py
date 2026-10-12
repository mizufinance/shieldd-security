from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
context=ROOT/'context';context.mkdir()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();start=text.index('    pub const fn neg(');end=text.index('\n}',start)
body=text[start:end];assert body.count('sbb(')==4 and body.count(' & mask')==4 and '.wrapping_sub(1)' in body
shape={'library':pin(library),'source_neg_body':body,'scope':'Exact authenticated cached Scalar neg source four SBB MODULUS-self and four-limb OR zero detector Boolean cast wrapping-subtract mask. Model symbolic left OR walk starts at zero; native primitive/compiler/private Scalar/caller bindings remain separate.'}
(context/'scalar-canonical-neg-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-canonical-sub-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-canonical-add-20261011-02'","UPSTREAM = DIAG / 'transfer-scalar-canonical-sub-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-canonical-sub-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-canonical-neg-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarCanonicalSub01'","MODULE = 'TransferScalarCanonicalNeg01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarCanonicalAdd01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarCanonicalSub01/stdout.txt'")
replace('assert len(current) == 5','assert len(current) == 3')
replace("records.append(('TransferScalarCanonicalAdd01'","records.append(('TransferScalarCanonicalSub01'")
replace("'handwritten/TransferScalarCanonicalAdd01.lean', 'project/ShielddSecurity/TransferScalarCanonicalAdd01.lean'","'handwritten/TransferScalarCanonicalSub01.lean', 'project/ShielddSecurity/TransferScalarCanonicalSub01.lean'")
s=s.replace('== 145','== 146').replace('== 1172','== 1175').replace("'objects': 145","'objects': 146").replace('one-hundred-forty-five-module','one-hundred-forty-six-module').replace('1172 inherited','1175 inherited').replace("'inherited_audits': 1172","'inherited_audits': 1175")
replace('assert len(names) == 3','assert len(names) == 6')
replace("'imports': ['ShielddSecurity.TransferScalarCanonicalAdd01']","'imports': ['ShielddSecurity.TransferScalarCanonicalSub01']")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Actual Scalar.neg four SBB MODULUS-self recurrence and OR-zero detector Boolean cast/wrapping-subtract mask derives four output limbs, canonical modular negation and exact zero handling from canonical raw operand. Three definitions/three theorem audits. Another private Scalar operation model; global constructor/other operation/private representation invariant and native Rust primitive/compiler/ABI/caller correspondence remain OPEN. No native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_canonical_sub_source_shape']=pin(ROOT/'context/scalar-canonical-sub-shape.json')","mapping['scalar_canonical_sub_source_shape']=pin(DIAG/'transfer-scalar-canonical-sub-20261011-02/context/scalar-canonical-sub-shape.json')\nmapping['scalar_canonical_neg_source_shape']=pin(ROOT/'context/scalar-canonical-neg-shape.json')")
replace("plan['pins'].append(mapping['scalar_canonical_sub_source_shape'])","plan['pins'].append(mapping['scalar_canonical_sub_source_shape'])\nplan['pins'].append(mapping['scalar_canonical_neg_source_shape'])")
s=s.replace("'fresh_audits': 3","'fresh_audits': 6").replace('SCALAR_CANONICAL_SUB_COMPLETE_ONE_HUNDRED_FORTY_FIVE_MODULE','SCALAR_CANONICAL_NEG_COMPLETE_ONE_HUNDRED_FORTY_SIX_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':1175,'owned_modules':146,'source_shape':pin(context/'scalar-canonical-neg-shape.json')})
