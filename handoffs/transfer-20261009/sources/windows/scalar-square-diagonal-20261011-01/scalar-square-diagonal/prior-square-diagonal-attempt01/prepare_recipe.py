from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=library.read_text();start=text.index('    pub const fn square(');end=text.index('\n    }',start)+6
body=text[start:end];diagonal=body[body.index('        let (r0, carry) ='):body.index('        Scalar::montgomery_reduce')]
assert diagonal.count('mac(')==4 and diagonal.count('adc(')==4
(ROOT/'context').mkdir()
(ROOT/'context/scalar-square-diagonal-shape.json').write_text(json.dumps({'library':pin(library),'square_body':body,'diagonal_mac_adc_assignments':diagonal,'scope':'Exact cached source four diagonal MAC/ADC pairs, final ignored carry and algebraic diagonal/cross reconstruction. Static association only; no native/compiler/caller credit.'},indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-square-shift-20261011-04/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-scalar-square-cross-20261011-02'","UPSTREAM = DIAG / 'transfer-scalar-square-shift-20261011-04'"),
 ("POOL = DIAG / 'transfer-scalar-square-shift-owned-floor-20261011-04'","POOL = DIAG / 'transfer-scalar-square-diagonal-owned-floor-20261011-01'"),
 ("MODULE = 'TransferScalarSquareShift01'","MODULE = 'TransferScalarSquareDiagonal01'"),
 ("stdout = UPSTREAM / 'runs/01-TransferScalarSquareCross01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarSquareShift01/stdout.txt'"),
 ('assert len(current) == 6','assert len(current) == 7'),
 ("records.append(('TransferScalarSquareCross01'","records.append(('TransferScalarSquareShift01'"),
 ("'handwritten/TransferScalarSquareCross01.lean', 'project/ShielddSecurity/TransferScalarSquareCross01.lean'","'handwritten/TransferScalarSquareShift01.lean', 'project/ShielddSecurity/TransferScalarSquareShift01.lean'"),
 ('assert len(names) == 7','assert len(names) == 4'),
 ("'imports': ['ShielddSecurity.TransferScalarSquareCross01']","'imports': ['ShielddSecurity.TransferScalarSquareShift01']")]:replace(a,b)
s=s.replace('== 152','== 153').replace('== 1206','== 1213').replace("'objects': 152","'objects': 153").replace('one-hundred-fifty-two-module','one-hundred-fifty-three-module').replace('1206 inherited','1213 inherited').replace("'inherited_audits': 1206","'inherited_audits': 1213")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Actual modeled source diagonal MAC/ADC pair recurrence derives retained width and full integer including final carry for arbitrary matching inputs. Symbolic diagonal plus twice cross terms equals exact packed integer square. Two definitions/two theorems. Final discarded carry, wide reduction/canonical square and native primitive/library/compiler/ABI/caller correspondence/full Transfer OPEN; no native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['scalar_square_shift_source_shape']=pin(ROOT/'context/scalar-square-shift-shape.json')","mapping['scalar_square_shift_source_shape']=pin(DIAG/'transfer-scalar-square-shift-20261011-04/context/scalar-square-shift-shape.json')\nmapping['scalar_square_diagonal_source_shape']=pin(ROOT/'context/scalar-square-diagonal-shape.json')")
replace("plan['pins'].append(mapping['scalar_square_shift_source_shape'])","plan['pins'].append(mapping['scalar_square_shift_source_shape'])\nplan['pins'].append(mapping['scalar_square_diagonal_source_shape'])")
s=s.replace("'fresh_audits': 7","'fresh_audits': 4").replace('SCALAR_SQUARE_SHIFT_COMPLETE_ONE_HUNDRED_FIFTY_TWO_MODULE','SCALAR_SQUARE_DIAGONAL_COMPLETE_ONE_HUNDRED_FIFTY_THREE_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':1213,'owned_modules':153})
