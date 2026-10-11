"""Install concrete proved typed-word pending codec in heterogeneous object tag."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
file=ROOT/'handwritten/TransferWordObjectCodec01.lean';source=file.read_text().removesuffix('end ShielddSecurity.TransferWordObjectCodec01\n')
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferWordObjectCodec01\n';file.write_text(source)
s=(DIAG/'transfer-canonical-word-pending-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
("UPSTREAM = DIAG / 'transfer-symbolic-field-map-20261011-01'","UPSTREAM = DIAG / 'transfer-canonical-word-pending-20261011-03'"),
("POOL = DIAG / 'transfer-canonical-word-pending-owned-floor-20261011-03'","POOL = DIAG / 'transfer-word-object-codec-owned-floor-20261011-01'"),
("MODULE = 'TransferCanonicalWordPending01'","MODULE = 'TransferWordObjectCodec01'"),
("stdout = UPSTREAM / 'runs/01-TransferSymbolicFieldMap01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferCanonicalWordPending01/stdout.txt'"),
('assert len(current) == 2','assert len(current) == 8'),
("records.append(('TransferSymbolicFieldMap01'","records.append(('TransferCanonicalWordPending01'"),
("    'handwritten/TransferSymbolicFieldMap01.lean', 'project/ShielddSecurity/TransferSymbolicFieldMap01.lean']]","    'handwritten/TransferCanonicalWordPending01.lean', 'project/ShielddSecurity/TransferCanonicalWordPending01.lean']]"),
('assert len(records) == 117 and len(audits) == 1015','assert len(records) == 118 and len(audits) == 1023'),
("'objects': 117","'objects': 118"),
("'imports': ['ShielddSecurity.TransferSymbolicFieldMap01']","'imports': ['ShielddSecurity.TransferCanonicalWordPending01']")]:replace(a,b)
s=s.replace('one-hundred-seventeen-module','one-hundred-eighteen-module').replace('1015 inherited','1023 inherited')
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Heterogeneous typed object tag contains finite pending fields as proved source-derived canonical raw Scalar vectors, with separate other-object/tree tag. Supported enum identity and restored observations, exact canonical bounded sealed getter and empty default derive from concrete field/list decoder codec. Eight reports four definitions/four theorems; no caller field inverse/codec roundtrip/getter correspondence premise. Old extended ghost carrier remains; no global erasure. Native imbl/private Scalar/Any/downcast/Clone/primitive/compiler/Choice/CtOption/ownership/full trace binding remains explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')\nmapping['wide_reduction_source_shape']=pin(DIAG/'transfer-scalar-wide-round-20261011-04/context/wide-reduction-shape.json')\nmapping['r2_decoder_payload_source_shape']=pin(DIAG/'transfer-scalar-r2-payload-20261011-01/context/r2-decoder-payload-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('CANONICAL_WORD_PENDING_COMPLETE_ONE_HUNDRED_SEVENTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WORD_OBJECT_CODEC_COMPLETE_ONE_HUNDRED_EIGHTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 1015","'inherited_audits': 1023")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':1023,'owned_modules':118,'native_credit':0})
