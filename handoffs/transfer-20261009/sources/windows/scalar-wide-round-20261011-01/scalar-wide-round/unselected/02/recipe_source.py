"""Fresh source-shaped four-MAC/upper-ADC round, deferred carry retained."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
data=library.read_bytes();assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=data.decode();a=text.index('    const fn montgomery_reduce(');b=text.index('    /// Multiplies',a);body=text[a:b]
assert body.count(' = mac(')==16 and body.count(' = adc(')==4
assert 'adc(r4, 0, carry)' in body and 'adc(r5, carry2, carry)' in body and 'adc(r6, carry2, carry)' in body and 'adc(r7, carry2, carry)' in body
(ROOT/'context').mkdir();shape={'library':{'path':str(library),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()},'body':body,'scope':'Four low-word INV and four4-MAC groups each followed by upper ADC including deferred carry2; final carry ignored by source. Static shape only; final zero carry/bound and source compiler/primitive/native trace binding require proof.'}
(ROOT/'context/wide-reduction-shape.json').write_text(json.dumps(shape,indent=2,sort_keys=True)+'\n')
file=ROOT/'handwritten/TransferScalarWideRound01.lean';source=file.read_text();source=source.removesuffix('end ShielddSecurity.TransferScalarWideRound01\n')
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==6
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarWideRound01\n';file.write_text(source)
s=(DIAG/'transfer-scalar-wide-product-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-choice-bit-20261011-01'", "UPSTREAM = DIAG / 'transfer-scalar-wide-product-20261011-01'")
replace("POOL = DIAG / 'transfer-scalar-wide-product-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-wide-round-owned-floor-20261011-02'")
replace("MODULE = 'TransferScalarWideProduct01'", "MODULE = 'TransferScalarWideRound01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarChoiceBit01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferScalarWideProduct01/stdout.txt'")
replace('assert len(current) == 8','assert len(current) == 7')
replace("records.append(('TransferScalarChoiceBit01'", "records.append(('TransferScalarWideProduct01'")
replace("    'handwritten/TransferScalarChoiceBit01.lean', 'project/ShielddSecurity/TransferScalarChoiceBit01.lean']]", "    'handwritten/TransferScalarWideProduct01.lean', 'project/ShielddSecurity/TransferScalarWideProduct01.lean']]")
replace('assert len(records) == 109 and len(audits) == 962','assert len(records) == 110 and len(audits) == 969')
replace("'objects': 109", "'objects': 110")
s=s.replace('one-hundred-nine-module','one-hundred-ten-module').replace('962 inherited','969 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarChoiceBit01']", "'imports': ['ShielddSecurity.TransferScalarWideProduct01']")
replace('assert len(names) == 7','assert len(names) == 6');replace("'fresh_audits': 7", "'fresh_audits': 6")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Source-shaped wide Montgomery low4 MAC/upper ADC row preserves pending carry2 as modeled state. Derives actual retained low word zero from source INV, four MAC shifted exact equation, remaining width and exact full integer conservation with deferred carry. Six reports two definitions/four theorems; no assumed cancellation or desired output or unrolled constraint walk. Native compiler/primitive/full trace and final four-round reduction/ignored carry bound remain explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')\nmapping['wide_reduction_source_shape']=pin(ROOT/'context/wide-reduction-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
at=s.index("plan['artifact_policy']");s=s[:at]+"plan['pins'].append(mapping['wide_reduction_source_shape'])\n"+s[at:]
s=s.replace('SCALAR_WIDE_PRODUCT_COMPLETE_ONE_HUNDRED_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_WIDE_ROUND_COMPLETE_ONE_HUNDRED_TEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 962", "'inherited_audits': 969")
s=s.replace("plan['artifact_policy']","plan['pins'] += [pin(DIAG/'transfer-scalar-wide-round-20261011-01/prepare_recipe.py'), pin(DIAG/'transfer-scalar-wide-round-20261011-01/handwritten/TransferScalarWideRound01.lean'), pin(ROOT/'recipe_source.py')]\nplan['artifact_policy']",1)
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':6,'inherited_reports':969,'owned_modules':110,'wide_full_reduction_open':True})
