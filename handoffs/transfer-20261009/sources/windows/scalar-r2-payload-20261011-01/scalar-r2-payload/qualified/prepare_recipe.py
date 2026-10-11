"""Capture pinned decoder R2 constant/use and prove actual modeled payload."""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
data=library.read_bytes();assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=data.decode();r2=re.search(r'const R2: Scalar = Scalar\(\[(.*?)\]\);',text,re.S);assert r2
words=[int(w.replace('_',''),16) for w in re.findall(r'0x[0-9a-f_]+',r2.group(1))]
assert words==[0xc999e990f3f29c6d,0x2b6cedcb87925c23,0x05d314967254398f,0x0748d9d99f59ff11]
a=text.index('    pub fn from_bytes(');b=text.index('    /// Converts',a);body=text[a:b]
assert 'tmp *= &R2;' in body and 'CtOption::new(tmp, Choice::from(is_some))' in body
(ROOT/'context').mkdir();(ROOT/'context/r2-decoder-payload-shape.json').write_text(json.dumps({'library':{'path':str(library),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()},'r2_definition':r2.group(0),'words':words,'decoder_body':body,'scope':'Exact R2 literal and from_bytes raw field parse/choice bit then tmp*=R2/CtOption constructor source association. Static only; native/compiler/private Scalar/Choice/CtOption/full trace binding separate.'},indent=2,sort_keys=True)+'\n')
file=ROOT/'handwritten/TransferScalarR2Payload01.lean';source=file.read_text().removesuffix('end ShielddSecurity.TransferScalarR2Payload01\n')
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==7
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarR2Payload01\n';file.write_text(source)
s=(DIAG/'transfer-scalar-wide-reduction-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-wide-walk-20261011-02'", "UPSTREAM = DIAG / 'transfer-scalar-wide-reduction-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-wide-reduction-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-r2-payload-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarWideReduction01'", "MODULE = 'TransferScalarR2Payload01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarWideWalk01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferScalarWideReduction01/stdout.txt'")
replace('assert len(current) == 7','assert len(current) == 8')
replace("records.append(('TransferScalarWideWalk01'", "records.append(('TransferScalarWideReduction01'")
replace("    'handwritten/TransferScalarWideWalk01.lean', 'project/ShielddSecurity/TransferScalarWideWalk01.lean']]", "    'handwritten/TransferScalarWideReduction01.lean', 'project/ShielddSecurity/TransferScalarWideReduction01.lean']]")
replace('assert len(records) == 112 and len(audits) == 982','assert len(records) == 113 and len(audits) == 990')
replace("'objects': 112", "'objects': 113")
s=s.replace('one-hundred-twelve-module','one-hundred-thirteen-module').replace('982 inherited','990 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarWideWalk01']", "'imports': ['ShielddSecurity.TransferScalarWideReduction01']")
replace('assert len(names) == 8','assert len(names) == 7');replace("'fresh_audits': 8", "'fresh_audits': 7")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Exact pinned R2 typed words have kernel-certified value/range/inverse relation. Decoder payload is constructed from actual modeled sixteen-MAC schoolbook product, four wide MAC/ADC rounds, proved discarded carry zero and exact masked subtraction; canonical raw Montgomery value and exact raw-mod-p serializer value are derived conclusions. Seven reports two definitions/five theorems. No desired payload constructor state or caller cancellation premise; native private Scalar/compiler/primitive/Choice/CtOption/full trace binding remains explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')\nmapping['wide_reduction_source_shape']=pin(DIAG/'transfer-scalar-wide-round-20261011-04/context/wide-reduction-shape.json')\nmapping['r2_decoder_payload_source_shape']=pin(ROOT/'context/r2-decoder-payload-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
at=s.index("plan['artifact_policy']");s=s[:at]+"plan['pins'].append(mapping['r2_decoder_payload_source_shape'])\n"+s[at:]
s=s.replace('SCALAR_WIDE_REDUCTION_COMPLETE_ONE_HUNDRED_TWELVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_R2_PAYLOAD_COMPLETE_ONE_HUNDRED_THIRTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 982", "'inherited_audits': 990")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_reports':990,'owned_modules':113,'native_credit':0})
