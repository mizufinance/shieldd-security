"""Join proved parser, finite choice bit and actual modeled R2 payload."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
file=ROOT/'handwritten/TransferScalarCanonicalDecoder01.lean';source=file.read_text().removesuffix('end ShielddSecurity.TransferScalarCanonicalDecoder01\n')
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarCanonicalDecoder01\n';file.write_text(source)
s=(DIAG/'transfer-scalar-r2-payload-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-wide-reduction-20261011-02'", "UPSTREAM = DIAG / 'transfer-scalar-r2-payload-20261011-01'")
replace("POOL = DIAG / 'transfer-scalar-r2-payload-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-scalar-canonical-decoder-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarR2Payload01'", "MODULE = 'TransferScalarCanonicalDecoder01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarWideReduction01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferScalarR2Payload01/stdout.txt'")
replace('assert len(current) == 8','assert len(current) == 7')
replace("records.append(('TransferScalarWideReduction01'", "records.append(('TransferScalarR2Payload01'")
replace("    'handwritten/TransferScalarWideReduction01.lean', 'project/ShielddSecurity/TransferScalarWideReduction01.lean']]", "    'handwritten/TransferScalarR2Payload01.lean', 'project/ShielddSecurity/TransferScalarR2Payload01.lean']]")
replace('assert len(records) == 113 and len(audits) == 990','assert len(records) == 114 and len(audits) == 997')
replace("'objects': 113", "'objects': 114")
s=s.replace('one-hundred-thirteen-module','one-hundred-fourteen-module').replace('990 inherited','997 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarWideReduction01']", "'imports': ['ShielddSecurity.TransferScalarR2Payload01']")
replace('assert len(names) == 7','assert len(names) == 8');replace("'fresh_audits': 7", "'fresh_audits': 8")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Constructed source decoder composes four typed LE word reads, exact finite borrow-choice byte and actual modeled R2 schoolbook/wide-Montgomery/subtract payload. Option is only a model success projection. Derives acceptance iff parsed integer below p, canonical payload/serialized value, accepted32byte exact reserialization and original canonical raw Scalar-vector recovery. Eight reports three definitions/five theorems; no supplied desired payload or codec roundtrip premise. Native private Scalar invariant/Choice/CtOption/primitive/compiler/full execution bindings remain explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')\nmapping['wide_reduction_source_shape']=pin(DIAG/'transfer-scalar-wide-round-20261011-04/context/wide-reduction-shape.json')\nmapping['r2_decoder_payload_source_shape']=pin(DIAG/'transfer-scalar-r2-payload-20261011-01/context/r2-decoder-payload-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('SCALAR_R2_PAYLOAD_COMPLETE_ONE_HUNDRED_THIRTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_CANONICAL_DECODER_COMPLETE_ONE_HUNDRED_FOURTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 990", "'inherited_audits': 997")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':997,'owned_modules':114,'native_credit':0})
