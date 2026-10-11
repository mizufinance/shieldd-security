"""Narrow symbolic field map needed to repair live pending codec kernel cost."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
file=ROOT/'handwritten/TransferSymbolicFieldMap01.lean';source=file.read_text().removesuffix('end ShielddSecurity.TransferSymbolicFieldMap01\n')
names=re.findall(r'^theorem ([A-Za-z0-9_]+)',source,re.M);assert len(names)==2
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferSymbolicFieldMap01\n';file.write_text(source)
s=(DIAG/'transfer-canonical-word-pending-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("POOL = DIAG / 'transfer-canonical-word-pending-owned-floor-20261011-02'","POOL = DIAG / 'transfer-symbolic-field-map-owned-floor-20261011-01'")
replace("MODULE = 'TransferCanonicalWordPending01'","MODULE = 'TransferSymbolicFieldMap01'")
replace('assert len(names) == 8','assert len(names) == 2');replace("'fresh_audits': 8","'fresh_audits': 2")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Small polymorphic finite list mapping contracts required by live source-derived typed pending field codec. Encoder/projector/reference are symbolic parameters; pointwise field equation derives exact list projection or list roundtrip. Two full theorem reports; no concrete field unfolding/native/negative-control/certification credit. Used to keep kernel checking within unchanged finite heartbeat/memory guards; complete failed concrete histories retained.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')\nmapping['wide_reduction_source_shape']=pin(DIAG/'transfer-scalar-wide-round-20261011-04/context/wide-reduction-shape.json')\nmapping['r2_decoder_payload_source_shape']=pin(DIAG/'transfer-scalar-r2-payload-20261011-01/context/r2-decoder-payload-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace("plan['artifact_policy']","failedWord02=DIAG/'transfer-canonical-word-pending-20261011-02'\nplan['pins'] += [pin(failedWord02/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCanonicalWordPending01.lean','project/ShielddSecurity/TransferCanonicalWordPending01.lean','runs/01-TransferCanonicalWordPending01/stdout.txt']]\nplan['artifact_policy']",1)
s=s.replace('CANONICAL_WORD_PENDING_COMPLETE_ONE_HUNDRED_SIXTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SYMBOLIC_FIELD_MAP_COMPLETE_ONE_HUNDRED_SIXTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':2,'inherited_reports':1013,'owned_modules':116,'native_credit':0})
