from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-checked-word-block-driver-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-checked-word-walk-20261011-01'","UPSTREAM = DIAG / 'transfer-checked-word-block-driver-20261011-03'"),
 ("POOL = DIAG / 'transfer-checked-word-block-driver-owned-floor-20261011-03'","POOL = DIAG / 'transfer-checked-word-known-finalization-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCheckedWordBlockDriver01'","MODULE = 'TransferCheckedWordKnownFinalization01'"),
 ('len(records) == 140 and len(audits) == 1148','len(records) == 141 and len(audits) == 1153'),
 ("'objects': 140","'objects': 141"),
 ('assert len(current) == 4','assert len(current) == 5'),
 ("'imports': ['ShielddSecurity.TransferCheckedWordWalk01']","'imports': ['ShielddSecurity.TransferCheckedWordBlockDriver01']"),
 ("'fresh_audits': 5, 'inherited_audits': 1148","'fresh_audits': 5, 'inherited_audits': 1153")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCheckedWordWalk01','TransferCheckedWordBlockDriver01')+s[end:]
s=s.replace('one-hundred-forty-module','one-hundred-forty-one-module').replace('1148 inherited full reports','1153 inherited full reports').replace('CHECKED_WORD_BLOCK_DRIVER_COMPLETE_ONE_HUNDRED_FORTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_KNOWN_FINALIZATION_COMPLETE_ONE_HUNDRED_FORTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Returned whole checked-word public batch/checked seal driver actual selected original canonical field getter survives six known corrected source-ordered finishing object mutations. Exact source key order and only tree put/deletion tombstones are derived, then generic symbolic frame preserves actual sealed object and all three SCT getters. Recipe tree value remains parameter; converter cannot receive unsupported ghost in constructed known recipe, exact value vector audited. Two definition/three theorem audits. Coverage is known operations only; hidden native callees/tree values/complete App trace/Any/Clone/imbl/ownership/compiler/full native bindings OPEN. No exhaustive native trace/replay/control/certification credit; all prior failures and metadata histories retained zero credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'checked_word_getter_after_known_six_mutations':True,'reports':5,'guards_unchanged':True})
