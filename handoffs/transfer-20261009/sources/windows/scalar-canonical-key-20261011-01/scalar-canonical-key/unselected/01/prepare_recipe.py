"""Construct canonical field representation from the proved source decoder."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
file=ROOT/'handwritten/TransferScalarCanonicalKey01.lean';source=file.read_text().removesuffix('end ShielddSecurity.TransferScalarCanonicalKey01\n')
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarCanonicalKey01\n';file.write_text(source)
s=(DIAG/'transfer-scalar-canonical-decoder-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
("UPSTREAM = DIAG / 'transfer-scalar-r2-payload-20261011-01'","UPSTREAM = DIAG / 'transfer-scalar-canonical-decoder-20261011-01'"),
("POOL = DIAG / 'transfer-scalar-canonical-decoder-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-canonical-key-owned-floor-20261011-01'"),
("MODULE = 'TransferScalarCanonicalDecoder01'","MODULE = 'TransferScalarCanonicalKey01'"),
("stdout = UPSTREAM / 'runs/01-TransferScalarR2Payload01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarCanonicalDecoder01/stdout.txt'"),
('assert len(current) == 7','assert len(current) == 8'),
("records.append(('TransferScalarR2Payload01'","records.append(('TransferScalarCanonicalDecoder01'"),
("    'handwritten/TransferScalarR2Payload01.lean', 'project/ShielddSecurity/TransferScalarR2Payload01.lean']]","    'handwritten/TransferScalarCanonicalDecoder01.lean', 'project/ShielddSecurity/TransferScalarCanonicalDecoder01.lean']]"),
('assert len(records) == 114 and len(audits) == 997','assert len(records) == 115 and len(audits) == 1005'),
("'objects': 114","'objects': 115"),
("'imports': ['ShielddSecurity.TransferScalarR2Payload01']","'imports': ['ShielddSecurity.TransferScalarCanonicalDecoder01']")]:replace(a,b)
s=s.replace('one-hundred-fourteen-module','one-hundred-fifteen-module').replace('997 inherited','1005 inherited')
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Every canonical natural nullifier key is constructed through actual modeled typed LE bytes/parser/choice/R2 decoder payload, yielding canonical raw Scalar words. Derives exact source key projection/serialization/decoder success, full canonical raw-vector inverse and key equality iff constructed raw-vector equality. Eight reports two definitions/six theorems; no chosen desired raw Montgomery output or assumed inverse codec. Native private Scalar/primitive/compiler/Choice/CtOption/collections/full trace bindings remain explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')\nmapping['wide_reduction_source_shape']=pin(DIAG/'transfer-scalar-wide-round-20261011-04/context/wide-reduction-shape.json')\nmapping['r2_decoder_payload_source_shape']=pin(DIAG/'transfer-scalar-r2-payload-20261011-01/context/r2-decoder-payload-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('SCALAR_CANONICAL_DECODER_COMPLETE_ONE_HUNDRED_FOURTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_CANONICAL_KEY_COMPLETE_ONE_HUNDRED_FIFTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 997", "'inherited_audits': 1005")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':1005,'owned_modules':115,'native_credit':0})
