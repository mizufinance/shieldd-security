from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
context=ROOT/'context';context.mkdir()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text()
bodies={}
for name in ['from_raw','double','add','sub','mul','neg']:
    start=text.index('    pub const fn '+name+'(')
    end=text.index('\n    }',start)+6
    bodies[name]=text[start:end]
assert 'self.add(self)' in bodies['double'] and '(&Scalar(val)).mul(&R2)' in bodies['from_raw']
shape={'library':pin(library),'source_operation_bodies':bodies,'represented_family':['arbitrary four-word from_raw','add','sub','mul','neg','double'], 'excluded':['square','pow','invert','from_bytes_wide','random','arbitrary private raw Scalar construction'],'scope':'Public operation family arithmetic model derived from authenticated cached bodies; sourceEval recursion carries only kernel-proved output contracts. No assumption that every native Scalar originates in this family; caller/program/Rust primitive/compiler coupling OPEN.'}
(context/'scalar-program-family-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-canonical-neg-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-canonical-sub-20261011-02'","UPSTREAM = DIAG / 'transfer-scalar-canonical-neg-20261011-03'")
replace("POOL = DIAG / 'transfer-scalar-canonical-neg-owned-floor-20261011-03'","POOL = DIAG / 'transfer-scalar-program-invariant-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarCanonicalNeg01'","MODULE = 'TransferScalarProgramInvariant01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarCanonicalSub01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarCanonicalNeg01/stdout.txt'")
replace('assert len(current) == 3','assert len(current) == 6')
replace("records.append(('TransferScalarCanonicalSub01'","records.append(('TransferScalarCanonicalNeg01'")
replace("'handwritten/TransferScalarCanonicalSub01.lean', 'project/ShielddSecurity/TransferScalarCanonicalSub01.lean'","'handwritten/TransferScalarCanonicalNeg01.lean', 'project/ShielddSecurity/TransferScalarCanonicalNeg01.lean'")
s=s.replace('== 146','== 147').replace('== 1175','== 1181').replace("'objects': 146","'objects': 147").replace('one-hundred-forty-six-module','one-hundred-forty-seven-module').replace('1175 inherited','1181 inherited').replace("'inherited_audits': 1175","'inherited_audits': 1181")
replace('assert len(names) == 6','assert len(names) == 4')
replace("'imports': ['ShielddSecurity.TransferScalarCanonicalSub01']","'imports': ['ShielddSecurity.TransferScalarCanonicalNeg01']")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Represented public Scalar operation family starts with arbitrary four-word raw inputs converted by modeled R2 multiplication, then modeled add/sub/mul/neg/double. Every actual eval output is constructed from proven operation width/canonical contracts, yielding canonical raw words and exact32 byte Montgomery keys without caller operand invariant premises. One inductive/two definitions/one theorem audit. Excludes square/pow/invert/from-wide/random/arbitrary private construction; does not establish every native Scalar originates in this family. Caller/program/private Scalar/Rust primitive/compiler/ABI correspondence OPEN. No native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_canonical_neg_source_shape']=pin(ROOT/'context/scalar-canonical-neg-shape.json')","mapping['scalar_canonical_neg_source_shape']=pin(DIAG/'transfer-scalar-canonical-neg-20261011-03/context/scalar-canonical-neg-shape.json')\nmapping['scalar_program_family_source_shape']=pin(ROOT/'context/scalar-program-family-shape.json')")
replace("plan['pins'].append(mapping['scalar_canonical_neg_source_shape'])","plan['pins'].append(mapping['scalar_canonical_neg_source_shape'])\nplan['pins'].append(mapping['scalar_program_family_source_shape'])")
s=s.replace("'fresh_audits': 6","'fresh_audits': 4").replace('SCALAR_CANONICAL_NEG_COMPLETE_ONE_HUNDRED_FORTY_SIX_MODULE','SCALAR_PROGRAM_INVARIANT_COMPLETE_ONE_HUNDRED_FORTY_SEVEN_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':1181,'owned_modules':147,'source_shape':pin(context/'scalar-program-family-shape.json')})
