"""Compose full modeled wide reduction and derive ignored carry/range."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
file=ROOT/'handwritten/TransferScalarWideReduction01.lean';source=file.read_text().removesuffix('end ShielddSecurity.TransferScalarWideReduction01\n')
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarWideReduction01\n';file.write_text(source)
s=(DIAG/'transfer-scalar-wide-walk-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-wide-round-20261011-04'", "UPSTREAM = DIAG / 'transfer-scalar-wide-walk-20261011-02'")
replace("POOL = DIAG / 'transfer-scalar-wide-walk-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-scalar-wide-reduction-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarWideWalk01'", "MODULE = 'TransferScalarWideReduction01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarWideRound01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferScalarWideWalk01/stdout.txt'")
replace('assert len(current) == 6','assert len(current) == 7')
replace("records.append(('TransferScalarWideRound01'", "records.append(('TransferScalarWideWalk01'")
replace("    'handwritten/TransferScalarWideRound01.lean', 'project/ShielddSecurity/TransferScalarWideRound01.lean']]", "    'handwritten/TransferScalarWideWalk01.lean', 'project/ShielddSecurity/TransferScalarWideWalk01.lean']]")
replace('assert len(records) == 111 and len(audits) == 975','assert len(records) == 112 and len(audits) == 982')
replace("'objects': 111", "'objects': 112")
s=s.replace('one-hundred-eleven-module','one-hundred-twelve-module').replace('975 inherited','982 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarWideRound01']", "'imports': ['ShielddSecurity.TransferScalarWideWalk01']")
replace('assert len(names) == 7','assert len(names) == 8');replace("'fresh_audits': 7", "'fresh_audits': 8")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Full source-shaped modeled wide reduction composes sixteen MAC rows/four deferred-carry ADCs and exact masked single subtraction. Canonical right operand derives full product range; symbolic bound and actual2p<R certificate derive final ignored carry zero/four-word width/canonical range/exact Montgomery product relation. Eight reports two definitions/six theorems; no supplied desired result or ignored carry or unrolled constraint walk. Native private Scalar invariant/compiler/primitive/full trace and pinned R2 decoder payload binding remain explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')\nmapping['wide_reduction_source_shape']=pin(DIAG/'transfer-scalar-wide-round-20261011-04/context/wide-reduction-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('SCALAR_WIDE_WALK_COMPLETE_ONE_HUNDRED_ELEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_WIDE_REDUCTION_COMPLETE_ONE_HUNDRED_TWELVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 975", "'inherited_audits': 982")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_reports':982,'owned_modules':112,'native_credit':0})
