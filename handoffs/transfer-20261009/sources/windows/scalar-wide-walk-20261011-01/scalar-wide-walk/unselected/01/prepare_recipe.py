"""Prepare symbolic wide-state Montgomery walk and shrinking range induction."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
file=ROOT/'handwritten/TransferScalarWideWalk01.lean';source=file.read_text().removesuffix('end ShielddSecurity.TransferScalarWideWalk01\n')
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==7
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarWideWalk01\n';file.write_text(source)
s=(DIAG/'transfer-scalar-wide-round-20261011-04/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-wide-product-20261011-01'", "UPSTREAM = DIAG / 'transfer-scalar-wide-round-20261011-04'")
replace("POOL = DIAG / 'transfer-scalar-wide-round-owned-floor-20261011-04'", "POOL = DIAG / 'transfer-scalar-wide-walk-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarWideRound01'", "MODULE = 'TransferScalarWideWalk01'")
replace("stdout = UPSTREAM / 'runs/01-TransferScalarWideProduct01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferScalarWideRound01/stdout.txt'")
replace('assert len(current) == 7','assert len(current) == 6')
replace("records.append(('TransferScalarWideProduct01'", "records.append(('TransferScalarWideRound01'")
replace("    'handwritten/TransferScalarWideProduct01.lean', 'project/ShielddSecurity/TransferScalarWideProduct01.lean']]", "    'handwritten/TransferScalarWideRound01.lean', 'project/ShielddSecurity/TransferScalarWideRound01.lean']]")
replace('assert len(records) == 110 and len(audits) == 969','assert len(records) == 111 and len(audits) == 975')
replace("'objects': 110", "'objects': 111")
s=s.replace('one-hundred-ten-module','one-hundred-eleven-module').replace('969 inherited','975 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarWideProduct01']", "'imports': ['ShielddSecurity.TransferScalarWideRound01']")
replace('assert len(names) == 6','assert len(names) == 7');replace("'fresh_audits': 6", "'fresh_audits': 7")
start=s.index('\nmapping = ');end=s.index("\nmapping['corrected_finalization_source_order']",start)
scope='Symbolic source-shaped wide Montgomery state walk derives remaining four-word width and exact modular relation for any finite round count. Finite UInt64 INV multiplier and exact MAC/ADC row equation derive shrinking integer range and final value below twice p. Seven reports two definitions/five theorems; no supplied cancellation, desired final state, ignored carry or unrolled constraint walk. Native compiler/primitive/full trace and final carry/normalization/R2 payload remain explicit; zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['scalar_decode_source_shape']=pin(DIAG/'transfer-scalar-byte-decode-20261011-02/context/decoder-shape.json')\nmapping['wide_product_source_shape']=pin(DIAG/'transfer-scalar-wide-product-20261011-01/context/wide-product-shape.json')\nmapping['wide_reduction_source_shape']=pin(DIAG/'transfer-scalar-wide-round-20261011-04/context/wide-reduction-shape.json')"+s[end:]
a="plan['source_repairs'] = ";start=s.index(a);end=s.index('\n',start);s=s[:start]+a+repr(scope)+s[end:]
s=s.replace('SCALAR_WIDE_ROUND_COMPLETE_ONE_HUNDRED_TEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_WIDE_WALK_COMPLETE_ONE_HUNDRED_ELEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 969", "'inherited_audits': 975")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_reports':975,'owned_modules':111,'native_credit':0})
