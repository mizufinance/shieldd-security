from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();source=(ROOT/'handwritten/TransferScalarPublicConstants01.lean').read_text()
constants={}
for constructor,name in [('twoInverse','TWO_INV'),('generator','GENERATOR'),('rootOfUnity','ROOT_OF_UNITY'),('rootOfUnityInverse','ROOT_OF_UNITY_INV'),('delta','DELTA')]:
    start=text.index('const '+name+': Scalar = Scalar([');end=text.index(';',start)+1
    declaration=text[start:end];words=[int(s.replace('_',''),16) for s in re.findall(r'0x[0-9a-f_]+',declaration)]
    line=next(line for line in source.splitlines() if line.startswith('  | .'+constructor+' =>'))
    leanWords=[int(s,16) for s in re.findall(r'0x[0-9a-f]+',line)]
    assert len(words)==4 and words==leanWords
    binding=next(line for line in text.splitlines() if 'const '+('MULTIPLICATIVE_GENERATOR' if name=='GENERATOR' else name)+': Self' in line)
    constants[constructor]={'declaration':declaration,'words':words,'public_binding':binding}
(ROOT/'context').mkdir()
(ROOT/'context/scalar-public-constants-shape.json').write_text(json.dumps({'library':pin(library),'constants':constants,'scope':'Exact cached five public PrimeField four-word literal constants and bindings compared to handwritten source literals. Static source identity only; arithmetic proofs establish bounds and named closed Montgomery values. Root order/DELTA exponent and native compiler/caller separate; private modulus/raw temporaries not claimed canonical.'},indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-invert-chain-20261011-05/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-invert-machine-20261011-01'","UPSTREAM = DIAG / 'transfer-scalar-invert-chain-20261011-05'"),
 ("POOL = DIAG / 'transfer-scalar-invert-chain-owned-floor-20261011-05'","POOL = DIAG / 'transfer-scalar-public-constants-owned-floor-20261011-01'"),
 ("MODULE = 'TransferScalarInvertChain01'","MODULE = 'TransferScalarPublicConstants01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarInvertMachine01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarInvertChain01/stdout.txt'"),
 ('assert len(current) == 20','assert len(current) == 12'),
 ("records.append(('TransferScalarInvertMachine01'","records.append(('TransferScalarInvertChain01'"),
 ("'handwritten/TransferScalarInvertMachine01.lean', 'project/ShielddSecurity/TransferScalarInvertMachine01.lean'","'generated/TransferScalarInvertChain01.lean', 'project/ShielddSecurity/TransferScalarInvertChain01.lean'"),
 ('assert len(names) == 12','assert len(names) == 6'),
 ("'imports': ['ShielddSecurity.TransferScalarInvertMachine01']","'imports': ['ShielddSecurity.TransferScalarInvertChain01']"),
 ("handwritten = ROOT / 'generated' / (MODULE + '.lean')","handwritten = ROOT / 'handwritten' / (MODULE + '.lean')")]:replace(a,b)
s=s.replace('== 157','== 158').replace('== 1257','== 1269').replace("'objects': 157","'objects': 158").replace('one-hundred-fifty-seven-module','one-hundred-fifty-eight-module').replace('1257 inherited','1269 inherited').replace("'inherited_audits': 1257","'inherited_audits': 1269")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Five exact cached source public PrimeField constants have derived canonical raw words and exact32-byte Montgomery serialization. Closed integer certificates establish TWO_INV=(p+1)/2, GENERATOR=7 and product of ROOT_OF_UNITY/ROOT_OF_UNITY_INV keys=1 modulo p. One inductive/two definitions/three theorems. Root orders/DELTA exponent, arbitrary private constructors and native library/compiler/ABI/caller/full Transfer OPEN; no native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_invert_chain_source_shape']=pin(ROOT/'context/scalar-invert-chain-shape.json')","mapping['scalar_invert_chain_source_shape']=pin(DIAG/'transfer-scalar-invert-chain-20261011-05/context/scalar-invert-chain-shape.json')\nmapping['scalar_public_constants_source_shape']=pin(ROOT/'context/scalar-public-constants-shape.json')")
replace("plan['pins'].append(mapping['scalar_invert_chain_source_shape'])","plan['pins'].append(mapping['scalar_invert_chain_source_shape'])\nplan['pins'].append(mapping['scalar_public_constants_source_shape'])")
replace("plan['pins'].append(pin(ROOT/'generate_source.py'))","plan['pins'].append(pin(DIAG/'transfer-scalar-invert-chain-20261011-05/generate_source.py'))")
s=s.replace("'fresh_audits': 12","'fresh_audits': 6").replace('SCALAR_INVERT_CHAIN_COMPLETE_ONE_HUNDRED_FIFTY_SEVEN_MODULE','SCALAR_PUBLIC_CONSTANTS_COMPLETE_ONE_HUNDRED_FIFTY_EIGHT_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':1269,'owned_modules':158,'five_source_literals_checked':True})
