from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-checked-word-walk-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-checked-word-stage-invariant-20261011-01'","UPSTREAM = DIAG / 'transfer-checked-word-walk-20261011-01'"),
 ("POOL = DIAG / 'transfer-checked-word-walk-owned-floor-20261011-01'","POOL = DIAG / 'transfer-checked-word-block-driver-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCheckedWordWalk01'","MODULE = 'TransferCheckedWordBlockDriver01'"),
 ('len(records) == 139 and len(audits) == 1144','len(records) == 140 and len(audits) == 1148'),
 ("'objects': 139","'objects': 140"),('len(names) == 4','len(names) == 5'),
 ('assert len(current) == 2','assert len(current) == 4'),
 ("'imports': ['ShielddSecurity.TransferCheckedWordStageInvariant01']","'imports': ['ShielddSecurity.TransferCheckedWordWalk01']"),
 ("'fresh_audits': 4, 'inherited_audits': 1144","'fresh_audits': 5, 'inherited_audits': 1148")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCheckedWordStageInvariant01','TransferCheckedWordWalk01')+s[end:]
s=s.replace('one-hundred-thirty-nine-module','one-hundred-forty-module').replace('1144 inherited full reports','1148 inherited full reports').replace('CHECKED_WORD_WALK_COMPLETE_ONE_HUNDRED_THIRTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_BLOCK_DRIVER_COMPLETE_ONE_HUNDRED_FORTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Constructed complete public checked-word batch walk then checked source seal derives actual returned intermediate execution, exact final selected Sealed object and actual ordered/isSealed/ensureSealed getters of entire original canonical source field vector, global source-key Nodup/capacity, every durable false lookup and other-key frames. Observed initial selected absence and whole-run returned success only; no caller intermediate walk/next state/getter/domain/reader/invariant/codec-inverse premise. Two definition/three theorem audits. Native source selector/cache/Any/Clone/imbl/Scalar/reader/compiler/ownership/async/full source trace bindings OPEN; prior failures and metadata histories retained zero credit; no native/control/replay/certification credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'constructed_whole_checked_word_source_driver':True,'reports':5,'guards_unchanged':True})
