from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-checked-word-nullify-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-checked-word-seal-publication-20261011-02'","UPSTREAM = DIAG / 'transfer-checked-word-nullify-20261011-01'"),
 ("POOL = DIAG / 'transfer-checked-word-nullify-owned-floor-20261011-01'","POOL = DIAG / 'transfer-checked-word-stage-invariant-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCheckedWordNullify01'","MODULE = 'TransferCheckedWordStageInvariant01'"),
 ('len(records) == 137 and len(audits) == 1136','len(records) == 138 and len(audits) == 1142'),
 ("'objects': 137","'objects': 138"),('len(names) == 6','len(names) == 2'),
 ('assert len(current) == 3','assert len(current) == 6'),
 ("'imports': ['ShielddSecurity.TransferCheckedWordSealPublication01']","'imports': ['ShielddSecurity.TransferCheckedWordNullify01']"),
 ("'fresh_audits': 6, 'inherited_audits': 1136","'fresh_audits': 2, 'inherited_audits': 1142")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCheckedWordSealPublication01','TransferCheckedWordNullify01')+s[end:]
s=s.replace('one-hundred-thirty-seven-module','one-hundred-thirty-eight-module').replace('1136 inherited full reports','1142 inherited full reports').replace('CHECKED_WORD_NULLIFY_COMPLETE_ONE_HUNDRED_THIRTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_STAGE_INVARIANT_COMPLETE_ONE_HUNDRED_THIRTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Returned checked source staging derives actual projected numeric inspection without caller typed/getter/reader/admission/inverse/desired-output premise, then propagates symbolic coherence/Nodup/capacity and exact ordered append plus all actual durable false lookups. Prior coherence and uniqueness are inductive state invariants. Two theorem audits. Native functional cache/Any/Clone/imbl/Scalar/reader/compiler/source selector/ownership/async/full trace bindings OPEN; all prior failures and metadata histories retained zero credit; no native/control/replay/certification credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'symbolic_checked_stage_invariant':True,'reports':2,'guards_unchanged':True})
