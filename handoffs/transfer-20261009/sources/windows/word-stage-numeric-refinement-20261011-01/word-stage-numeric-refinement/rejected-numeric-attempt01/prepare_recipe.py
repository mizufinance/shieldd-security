from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-word-stage-admission-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-stage-order-20261011-02'","UPSTREAM = DIAG / 'transfer-word-stage-admission-20261011-02'"),
 ("POOL = DIAG / 'transfer-word-stage-admission-owned-floor-20261011-02'","POOL = DIAG / 'transfer-word-stage-numeric-refinement-owned-floor-20261011-01'"),
 ("MODULE = 'TransferWordStageAdmission01'","MODULE = 'TransferWordStageNumericRefinement01'"),
 ('len(records) == 131 and len(audits) == 1101','len(records) == 132 and len(audits) == 1107'),
 ("'objects': 131","'objects': 132"),
 ("'imports': ['ShielddSecurity.TransferWordStageOrder01']","'imports': ['ShielddSecurity.TransferWordStageAdmission01']"),
 ("'fresh_audits': 6, 'inherited_audits': 1101","'fresh_audits': 6, 'inherited_audits': 1107")]:replace(a,b)
replace('assert len(current) == 8','assert len(current) == 6')
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordStageOrder01','TransferWordStageAdmission01')+s[end:]
s=s.replace('one-hundred-thirty-one-module','one-hundred-thirty-two-module').replace('1101 inherited full reports','1107 inherited full reports').replace('WORD_STAGE_ADMISSION_COMPLETE_ONE_HUNDRED_THIRTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WORD_STAGE_NUMERIC_REFINEMENT_COMPLETE_ONE_HUNDRED_THIRTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Concrete canonical typed Open pending branch and modeled durable reader derive exact correspondence of every stage refusal/success to existing numeric inspection followed by original typed field append. Pending source Ord freshness equals numeric finite-membership freshness; no caller inverse/admission/desired-object/getter-success premise. Returned typed stage derives exact numeric pending append and all modeled durable lookup statuses false plus pending absence. Previous object is explicitly typed Open constructor, not arbitrary native Any or global walk domain. Two definitions/four theorem audits. Native durable-reader/collections/Scalar/usize/compiler/async/delta/full source trace correspondence OPEN. Prior rejected lint/pressure histories retained zero credit; no accepted ancestor replay/native/control/certification credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("mapping['scope'] += ");end=s.index("mapping_file = ROOT / 'source-mapping.json'",start)
s=s[:start]+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
start=s.index("plan['source_repairs'] += ");end=s.index('\n',start)
s=s[:start]+s[end+1:]
(ROOT/'prepare.py').write_text(s)
print({'typed_open_numeric_inspection_refinement':True,'reports':6,'guards_unchanged':True})
