from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
context=ROOT/'context';context.mkdir()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();start=text.index('    fn from_u512(');end=text.index('\n    }',start)+6
body=text[start:end];r3start=text.index('const R3:');r3=text[r3start:text.index('\n]);',r3start)+4]
assert 'd0 * R2 + d1 * R3' in body and all('limbs['+str(i)+']' in body for i in range(8))
shape={'library':pin(library),'from_u512_body':body,'R3_literal':r3,'scope':'Exact authenticated cached from_u512 low/high four-word indices, two mul R2/R3 then add, literal R3. Arithmetic model arbitrary digits; native 64 LE bytes/eight index split/private Scalar/primitive/compiler/caller bindings separate.'}
(context/'scalar-wide-constructor-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-program-invariant-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-canonical-neg-20261011-03'","UPSTREAM = DIAG / 'transfer-scalar-program-invariant-20261011-01'")
replace("POOL = DIAG / 'transfer-scalar-program-invariant-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-wide-constructor-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarProgramInvariant01'","MODULE = 'TransferScalarWideConstructor01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarCanonicalNeg01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarProgramInvariant01/stdout.txt'")
replace('assert len(current) == 6','assert len(current) == 4')
replace("records.append(('TransferScalarCanonicalNeg01'","records.append(('TransferScalarProgramInvariant01'")
replace("'handwritten/TransferScalarCanonicalNeg01.lean', 'project/ShielddSecurity/TransferScalarCanonicalNeg01.lean'","'handwritten/TransferScalarProgramInvariant01.lean', 'project/ShielddSecurity/TransferScalarProgramInvariant01.lean'")
s=s.replace('== 147','== 148').replace('== 1181','== 1185').replace("'objects': 147","'objects': 148").replace('one-hundred-forty-seven-module','one-hundred-forty-eight-module').replace('1181 inherited','1185 inherited').replace("'inherited_audits': 1181","'inherited_audits': 1185")
replace('assert len(names) == 4','assert len(names) == 6')
replace("'imports': ['ShielddSecurity.TransferScalarCanonicalNeg01']","'imports': ['ShielddSecurity.TransferScalarProgramInvariant01']")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Actual from_u512 low/high arbitrary four-word digits multiply R2/R3 then add in actual modeled MAC/wide reduction/ADC/sub recurrences. Exact R3 literal/inverse relation derives canonical high payload, then canonical wide payload and exact serialization of complete512-bit integer modulo p without caller canonical raw inputs. Three definitions/three theorem audits. Native64 LE reads/eight-index split/private Scalar/primitive/compiler/ABI/caller correspondence OPEN. No native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_program_family_source_shape']=pin(ROOT/'context/scalar-program-family-shape.json')","mapping['scalar_program_family_source_shape']=pin(DIAG/'transfer-scalar-program-invariant-20261011-01/context/scalar-program-family-shape.json')\nmapping['scalar_wide_constructor_source_shape']=pin(ROOT/'context/scalar-wide-constructor-shape.json')")
replace("plan['pins'].append(mapping['scalar_program_family_source_shape'])","plan['pins'].append(mapping['scalar_program_family_source_shape'])\nplan['pins'].append(mapping['scalar_wide_constructor_source_shape'])")
s=s.replace("'fresh_audits': 4","'fresh_audits': 6").replace('SCALAR_PROGRAM_INVARIANT_COMPLETE_ONE_HUNDRED_FORTY_SEVEN_MODULE','SCALAR_WIDE_CONSTRUCTOR_COMPLETE_ONE_HUNDRED_FORTY_EIGHT_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':1185,'owned_modules':148,'source_shape':pin(context/'scalar-wide-constructor-shape.json')})
