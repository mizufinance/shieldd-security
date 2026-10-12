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
    start=text.index(marker);return text[start:text.index('\n    }',start)+6]
fromU64=body('    fn from(val: u64)');randomBody=body('    fn random(mut rng: impl RngCore)');selectBody=body('    fn conditional_select(')
assert 'Scalar([val, 0, 0, 0]) * R2' in fromU64 and 'from_bytes_wide' in randomBody and 'fill_bytes' in randomBody
(ROOT/'context').mkdir()
(ROOT/'context/scalar-extended-family-shape.json').write_text(json.dumps({'library':pin(library),'from_u64_body':fromU64,'random_body':randomBody,'conditional_selection_body':selectBody,'represented_constructor_family':['prior raw4/wide64/canonical bytes32 and add/sub/mul/neg/double input programs','five public constants','zero','one','fromU64','random64 byte input','add','sub','mul','neg','double','optimized square','pow','pow_vartime','exact source invert chain','Boolean selection'],'open':['native RNG/Choice/wordwise conditional selection/ct_eq/compiler/caller/public API origin','arbitrary private raw constructor escape','generic trait/helper caller trace beyond explicit represented program','mathematical exponent/inverse semantics','full Transfer certification'],'scope':'Exact source API static associations and explicit represented family inventory; derive bounds solely from constructors and proved operation outputs. Native library/compiler/caller origin separate.'},indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-public-constants-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-invert-chain-20261011-05'","UPSTREAM = DIAG / 'transfer-scalar-public-constants-20261011-02'"),
 ("POOL = DIAG / 'transfer-scalar-public-constants-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-extended-family-owned-floor-20261012-01'"),
 ("MODULE = 'TransferScalarPublicConstants01'","MODULE = 'TransferScalarExtendedFamily01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarInvertChain01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarPublicConstants01/stdout.txt'"),
 ('assert len(current) == 12','assert len(current) == 6'),
 ("records.append(('TransferScalarInvertChain01'","records.append(('TransferScalarPublicConstants01'"),
 ("'generated/TransferScalarInvertChain01.lean', 'project/ShielddSecurity/TransferScalarInvertChain01.lean'","'handwritten/TransferScalarPublicConstants01.lean', 'project/ShielddSecurity/TransferScalarPublicConstants01.lean'"),
 ('assert len(names) == 6','assert len(names) == 4'),
 ("'imports': ['ShielddSecurity.TransferScalarInvertChain01']","'imports': ['ShielddSecurity.TransferScalarPublicConstants01']")]:replace(a,b)
s=s.replace('== 158','== 159').replace('== 1269','== 1275').replace("'objects': 158","'objects': 159").replace('one-hundred-fifty-eight-module','one-hundred-fifty-nine-module').replace('1269 inherited','1275 inherited').replace("'inherited_audits': 1269","'inherited_audits': 1275")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Extended represented returned Scalar source program includes prior arbitrary raw4/wide64/canonical32-byte constructors and operations, five public constants/ZERO/ONE/u64/random64-byte input, add/sub/mul/neg/double/optimized square/pow/pow_vartime/exact source inversion/Boolean selection. Every returned field derives canonical raw words and exact32-byte Montgomery key without caller operand invariant; inversion refusal derives prior construction failure or exact modeled zero payload. One inductive/one definition/two theorems. Native RNG/Choice/ct_eq/wordwise selection/public API origin/library/compiler/ABI/caller/generic helper trace, field exponent/inverse/full Transfer OPEN; no native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_public_constants_source_shape']=pin(ROOT/'context/scalar-public-constants-shape.json')","mapping['scalar_public_constants_source_shape']=pin(DIAG/'transfer-scalar-public-constants-20261011-02/context/scalar-public-constants-shape.json')\nmapping['scalar_extended_family_source_shape']=pin(ROOT/'context/scalar-extended-family-shape.json')")
replace("plan['pins'].append(mapping['scalar_public_constants_source_shape'])","plan['pins'].append(mapping['scalar_public_constants_source_shape'])\nplan['pins'].append(mapping['scalar_extended_family_source_shape'])")
s=s.replace("'fresh_audits': 6","'fresh_audits': 4").replace('SCALAR_PUBLIC_CONSTANTS_COMPLETE_ONE_HUNDRED_FIFTY_EIGHT_MODULE','SCALAR_EXTENDED_FAMILY_COMPLETE_ONE_HUNDRED_FIFTY_NINE_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':1275,'owned_modules':159})
