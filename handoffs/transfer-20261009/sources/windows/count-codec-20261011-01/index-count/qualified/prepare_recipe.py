"""Prepare a fresh narrow current-count proof from the unchanged guarded recipe."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-ordinary-index-read-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-volume-height-keys-20261011-01'", "UPSTREAM = DIAG / 'transfer-ordinary-index-read-20261011-01'")
s=s.replace('transfer-ordinary-index-read-owned-floor-20261011-01','transfer-ordinary-index-count-owned-floor-20261011-01')
s=s.replace("MODULE = 'TransferOrdinaryIndexReadSource01'", "MODULE = 'TransferOrdinaryIndexCountSource01'")
s=s.replace('TransferVolumeHeightKeys01','TransferOrdinaryIndexReadSource01')
replace('assert len(current) == 9','assert len(current) == 7')
replace("'portable-source/TransferOrdinaryIndexReadSource01.lean'", "'handwritten/TransferOrdinaryIndexReadSource01.lean'")
replace('assert len(records) == 20 and len(audits) == 243','assert len(records) == 21 and len(audits) == 250')
replace("'objects': 20", "'objects': 21")
s=s.replace('Complete twenty-module first owned root; 243 inherited full reports.','Complete twenty-one-module first owned root; 250 inherited full reports.')
replace('assert len(names) == 7','assert len(names) == 6')
start=s.index("mapping = {'runtime_sha'")
end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Actual modeled current-overlay NV count reads: inspection success derives available read, actual count observation and checked increment bound. Available malformed bytes derive countDecode, and available decoded full count derives overflow after actual conversion and absent identifier. Those preceding observations are explicit, rather than desired errors. Whole same-action Ordinary per-transaction delivery is refused when the original parent count is malformed or decodes to a saturated ordinal, with actual original decoded height and source-separated volume/height keys; body NV frame preserves the count through every body outcome. Whole refusal assumes neither body success, stable callbacks, desired index error nor rollback poststate. Enclosing finish preserves parent and queue. Native read/decoder/codec/key/proof/token/store/tree/block/durability correspondence remains open. No runtime controls or fresh native evidence.'}
""".rstrip()+s[end:]
s=s.replace('CURRENT_OVERLAY_INDEX_READS_DERIVE_WHOLE_ORDINARY_DUPLICATE_ID_REFUSAL','CURRENT_OVERLAY_COUNT_DERIVES_WHOLE_ORDINARY_MALFORMED_OR_OVERFLOW_REFUSAL')
s=s.replace('ORDINARY_INDEX_READ_COMPLETE_TWENTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','ORDINARY_INDEX_COUNT_COMPLETE_TWENTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 7, 'inherited_audits': 243", "'fresh_audits': 6, 'inherited_audits': 250")
s=s.replace('complete twenty-module owned root','complete twenty-one-module owned root')
s=s.replace('Fresh finite source installs NV read primitives and proves existing-parent duplicate refusal through the qualified whole Ordinary source.','Fresh finite source consumes actual NV reads and derives malformed/overflow refusal through the qualified whole Ordinary source.')
(ROOT/'prepare.py').write_text(s)
f=ROOT/'handwritten/TransferOrdinaryIndexCountSource01.lean'
lean=f.read_text()
names=re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)',lean,re.M)
assert len(names)==6 and '#check' not in lean
audits='\n'.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n for n in names)
lean=lean.replace('\nend ShielddSecurity.TransferOrdinaryIndexCountSource01','\n'+audits+'\n\nend ShielddSecurity.TransferOrdinaryIndexCountSource01')
f.write_text(lean)
print({'fresh_audits':6,'inherited_audits':250,'owned_modules':21})
