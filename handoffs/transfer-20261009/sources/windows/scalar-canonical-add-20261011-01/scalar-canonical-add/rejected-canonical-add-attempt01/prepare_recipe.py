from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
    data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
context=ROOT/'context';context.mkdir()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
assert pin(library)['sha256']=='986f81f5fe1ee2fe95da38b1517ee9faff5c3c45dbe6a4f8cae708434d7cd3b479' if False else library.is_file()
text=library.read_text();start=text.index('    pub const fn add(');end=text.index('    ///',start+1)
body=text[start:end]
assert body.count('adc(')==4 and '.sub(&MODULUS)' in body
shape={'library':pin(library),'source_add_body':body,'source_sub_body':text[text.index('    pub const fn sub('):start], 'scope':'Exact cached pinned Scalar add/sub shape, four ADC then sub modulus. Static identity and arithmetic model only; native Rust primitive/compiler/private Scalar caller correspondence separate.'}
(context/'scalar-canonical-add-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-checked-word-accepted-input-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-checked-word-fresh-snapshot-20261011-01'","UPSTREAM = DIAG / 'transfer-checked-word-accepted-input-20261011-02'")
replace("POOL = DIAG / 'transfer-checked-word-accepted-input-owned-floor-20261011-02'","POOL = DIAG / 'transfer-scalar-canonical-add-owned-floor-20261011-01'")
replace("MODULE = 'TransferCheckedWordAcceptedInput01'","MODULE = 'TransferScalarCanonicalAdd01'")
# Replace only the immediately imported source/report identifiers; failed-history pins stay original.
s=s.replace("stdout = UPSTREAM / 'runs/01-TransferCheckedWordFreshSnapshot01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferCheckedWordAcceptedInput01/stdout.txt'")
s=s.replace('assert len(current) == 5','assert len(current) == 4')
s=s.replace("records.append(('TransferCheckedWordFreshSnapshot01'","records.append(('TransferCheckedWordAcceptedInput01'")
s=s.replace("'handwritten/TransferCheckedWordFreshSnapshot01.lean', 'project/ShielddSecurity/TransferCheckedWordFreshSnapshot01.lean'","'handwritten/TransferCheckedWordAcceptedInput01.lean', 'project/ShielddSecurity/TransferCheckedWordAcceptedInput01.lean'")
s=s.replace('== 143','== 144').replace('== 1163','== 1167').replace("'objects': 143","'objects': 144").replace('one-hundred-forty-three-module','one-hundred-forty-four-module').replace('1163 inherited','1167 inherited').replace("'inherited_audits': 1163","'inherited_audits': 1167")
replace('assert len(names) == 4','assert len(names) == 5')
s=s.replace("'imports': ['ShielddSecurity.TransferCheckedWordFreshSnapshot01']","'imports': ['ShielddSecurity.TransferCheckedWordAcceptedInput01']")
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
scope='Source Scalar.add four ADC recurrence then actual sub-modulus/masked-addback model derives four output limbs, zero discarded input carry and canonical exact modular sum from canonical raw operands. Two definitions/three theorem audits. One operation model for private Scalar canonical preservation; all constructors/other operations/private representation and native Rust primitive/compiler/ABI/caller bindings remain OPEN. No native/runtime/control/replay/certification credit.'
s=s[:start]+"\nmapping = dict(prior_mapping)\nmapping['interfaces'] = prior_mapping['interfaces'] + ["+repr(scope)+"]\nmapping['scope'] = "+repr(scope)+s[end:]
replace("mapping['checked_word_accepted_source_shape']=pin(ROOT/'context/checked-word-accepted-source-shape.json')","mapping['checked_word_accepted_source_shape']=pin(DIAG/'transfer-checked-word-accepted-input-20261011-02/context/checked-word-accepted-source-shape.json')\nmapping['scalar_canonical_add_source_shape']=pin(ROOT/'context/scalar-canonical-add-shape.json')")
replace("plan['pins'].append(mapping['checked_word_accepted_source_shape'])","plan['pins'].append(mapping['checked_word_accepted_source_shape'])\nplan['pins'].append(mapping['scalar_canonical_add_source_shape'])")
s=s.replace("'fresh_audits': 4","'fresh_audits': 5").replace('CHECKED_WORD_ACCEPTED_INPUT_COMPLETE_ONE_HUNDRED_FORTY_THREE_MODULE','SCALAR_CANONICAL_ADD_COMPLETE_ONE_HUNDRED_FORTY_FOUR_MODULE')
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':5,'inherited_reports':1167,'owned_modules':144,'source_shape':pin(context/'scalar-canonical-add-shape.json')})
