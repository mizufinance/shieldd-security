from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-checked-word-stage-invariant-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-checked-word-nullify-20261011-01'","UPSTREAM = DIAG / 'transfer-checked-word-stage-invariant-20261011-01'"),
 ("POOL = DIAG / 'transfer-checked-word-stage-invariant-owned-floor-20261011-01'","POOL = DIAG / 'transfer-checked-word-walk-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCheckedWordStageInvariant01'","MODULE = 'TransferCheckedWordWalk01'"),
 ('len(records) == 138 and len(audits) == 1142','len(records) == 139 and len(audits) == 1144'),
 ("'objects': 138","'objects': 139"),('len(names) == 2','len(names) == 4'),
 ('assert len(current) == 6','assert len(current) == 2'),
 ("'imports': ['ShielddSecurity.TransferCheckedWordNullify01']","'imports': ['ShielddSecurity.TransferCheckedWordStageInvariant01']"),
 ("'fresh_audits': 2, 'inherited_audits': 1142","'fresh_audits': 4, 'inherited_audits': 1144")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCheckedWordNullify01','TransferCheckedWordStageInvariant01')+s[end:]
s=s.replace('one-hundred-thirty-eight-module','one-hundred-thirty-nine-module').replace('1142 inherited full reports','1144 inherited full reports').replace('CHECKED_WORD_STAGE_INVARIANT_COMPLETE_ONE_HUNDRED_THIRTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_WALK_COMPLETE_ONE_HUNDRED_THIRTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Symbolic whole public checked-word source batch walk updates actual selected functional cache slot each nonempty stage, skips empty batches and refuses missing source. Returned success derives actual each-stage/remaining walk, propagates input numeric coherence/Nodup to final coherence/Nodup/capacity, exact global original source-key order, every durable false lookup and all other-key frames. Input invariant is inductive state invariant, no chosen next state/codec/getter/reader success premise. One definition/three theorem audits. Native source selector, cache/Any/Clone/imbl/Scalar/reader/compiler/ownership/async/full trace bindings OPEN; all prior failure/metadata histories retained zero credit; no native/control/replay/certification credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'symbolic_actual_checked_word_walk':True,'reports':4,'guards_unchanged':True})
