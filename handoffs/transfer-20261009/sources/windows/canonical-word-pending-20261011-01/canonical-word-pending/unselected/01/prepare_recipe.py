"""Concrete finite pending fields use actual modeled canonical decoder construction."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
file=ROOT/'handwritten/TransferCanonicalWordPending01.lean';source=file.read_text().removesuffix('end ShielddSecurity.TransferCanonicalWordPending01\n')
names=re.findall(r'^(?:inductive|def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferCanonicalWordPending01\n';file.write_text(source)
s=(DIAG/'transfer-scalar-canonical-key-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
("UPSTREAM = DIAG / 'transfer-scalar-canonical-decoder-20261011-01'","UPSTREAM = DIAG / 'transfer-scalar-canonical-key-20261011-03'"),
("POOL = DIAG / 'transfer-scalar-canonical-key-owned-floor-20261011-03'","POOL = DIAG / 'transfer-canonical-word-pending-owned-floor-20261011-01'"),
("MODULE = 'TransferScalarCanonicalKey01'","MODULE = 'TransferCanonicalWordPending01'"),
("stdout = UPSTREAM / 'runs/01-TransferScalarCanonicalDecoder01/stdout.txt'","stdout = UPSTREAM / 'runs/01-TransferScalarCanonicalKey01/stdout.txt'"),
("records.append(('TransferScalarCanonicalDecoder01'","records.append(('TransferScalarCanonicalKey01'"),
("    'handwritten/TransferScalarCanonicalDecoder01.lean', 'project/ShielddSecurity/TransferScalarCanonicalDecoder01.lean']]","    'handwritten/TransferScalarCanonicalKey01.lean', 'project/ShielddSecurity/TransferScalarCanonicalKey01.lean']]"),
('assert len(records) == 115 and len(audits) == 1005','assert len(records) == 116 and len(audits) == 1013'),
("'objects': 115","'objects': 116"),
("'imports': ['ShielddSecurity.TransferScalarCanonicalDecoder01']","'imports': ['ShielddSecurity.TransferScalarCanonicalKey01']")]:replace(a,b)
s=s.replace('one-hundred-fifteen-module','one-hundred-sixteen-module').replace('1005 inherited','1013 inherited')
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Concrete finite pending enum fields are canonical typed raw Scalar vectors constructed through actual modeled LE/parser/choice/R2 decoder. Source key projection gives key mod p for arbitrary Nat; supported canonical finite enum/list fields derive exact roundtrip and coherent bounded current Pending restoration. Eight reports three definitions/one inductive/four theorems; no arbitrary field inverse/roundtrip premise. Seen set remains extensional finite member list; native private Scalar/imbl containers/Clone/Any/primitive/compiler/Choice/CtOption/full trace bindings remain explicit. Unsupported Nat keys wrap and receive no exact roundtrip claim; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')\nmapping['wide_reduction_source_shape']=pin(DIAG/'transfer-scalar-wide-round-20261011-04/context/wide-reduction-shape.json')\nmapping['r2_decoder_payload_source_shape']=pin(DIAG/'transfer-scalar-r2-payload-20261011-01/context/r2-decoder-payload-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('SCALAR_CANONICAL_KEY_COMPLETE_ONE_HUNDRED_FIFTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CANONICAL_WORD_PENDING_COMPLETE_ONE_HUNDRED_SIXTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 1005", "'inherited_audits': 1013")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':1013,'owned_modules':116,'native_credit':0})
