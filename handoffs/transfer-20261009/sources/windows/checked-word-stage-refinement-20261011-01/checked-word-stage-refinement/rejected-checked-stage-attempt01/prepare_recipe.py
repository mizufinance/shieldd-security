from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-word-stage-numeric-refinement-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-stage-admission-20261011-02'","UPSTREAM = DIAG / 'transfer-word-stage-numeric-refinement-20261011-03'"),
 ("POOL = DIAG / 'transfer-word-stage-numeric-refinement-owned-floor-20261011-03'","POOL = DIAG / 'transfer-checked-word-stage-refinement-owned-floor-20261011-01'"),
 ("MODULE = 'TransferWordStageNumericRefinement01'","MODULE = 'TransferCheckedWordStageRefinement01'"),
 ('len(records) == 132 and len(audits) == 1107','len(records) == 133 and len(audits) == 1113'),
 ("'objects': 132","'objects': 133"),
 ('len(names) == 6','len(names) == 8'),
 ("'imports': ['ShielddSecurity.TransferWordStageAdmission01']","'imports': ['ShielddSecurity.TransferWordStageNumericRefinement01']"),
 ("'fresh_audits': 6, 'inherited_audits': 1107","'fresh_audits': 8, 'inherited_audits': 1113")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordStageAdmission01','TransferWordStageNumericRefinement01')+s[end:]
s=s.replace('one-hundred-thirty-two-module','one-hundred-thirty-three-module').replace('1107 inherited full reports','1113 inherited full reports').replace('WORD_STAGE_NUMERIC_REFINEMENT_COMPLETE_ONE_HUNDRED_THIRTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_STAGE_REFINEMENT_COMPLETE_ONE_HUNDRED_THIRTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='All previous source-shaped object branches stage result erasure to checked numeric inspection, preserving duplicate-before-access, wrong-type outer panic and Sealed/other returned refusals. Concrete modeled durable reader derives previous membership from actual previous parameter; no caller typed-Open/getter/admission/inverse/desired-next-object premise. Successful staging projects to successful numeric stage; original word append projects to exact native-model pending append. Old wrong-type default projection never participates in returned successful staging because checked access rejects it. Pure duplicate test repeated inside numeric wrapper; semantic result equality only, no identical native trace claim. Four definitions/four theorem audits. Native Any/TypeId/Ord/Scalar/reader/usize/compiler/async/delta/full trace bindings OPEN; no native/control/certification or accepted ancestor replay credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("mapping['scope'] += ");end=s.index("mapping_file = ROOT / 'source-mapping.json'",start)
s=s[:start]+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s='\n'.join(line for line in s.split('\n') if not line.startswith("plan['source_repairs'] += "))
(ROOT/'prepare.py').write_text(s)
print({'all_checked_previous_branch_stage_refinement':True,'reports':8,'guards_unchanged':True})
