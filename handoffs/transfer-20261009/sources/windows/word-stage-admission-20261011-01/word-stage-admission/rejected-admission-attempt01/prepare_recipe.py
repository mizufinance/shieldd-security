from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-word-stage-order-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-canonical-source-membership-20261011-02'","UPSTREAM = DIAG / 'transfer-word-stage-order-20261011-02'"),
 ("POOL = DIAG / 'transfer-word-stage-order-owned-floor-20261011-02'","POOL = DIAG / 'transfer-word-stage-admission-owned-floor-20261011-01'"),
 ("MODULE = 'TransferWordStageOrder01'","MODULE = 'TransferWordStageAdmission01'"),
 ('len(records) == 130 and len(audits) == 1093','len(records) == 131 and len(audits) == 1101'),
 ("'objects': 130","'objects': 131"),
 ('len(names) == 8','len(names) == 6'),
 ('assert len(current) == 6','assert len(current) == 8'),
 ("'imports': ['ShielddSecurity.TransferCanonicalSourceMembership01']","'imports': ['ShielddSecurity.TransferWordStageOrder01']"),
 ("'fresh_audits': 8, 'inherited_audits': 1093","'fresh_audits': 6, 'inherited_audits': 1101")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCanonicalSourceMembership01','TransferWordStageOrder01')+s[end:]
s=s.replace('one-hundred-thirty-module','one-hundred-thirty-one-module').replace('1093 inherited full reports','1101 inherited full reports').replace('WORD_STAGE_ORDER_COMPLETE_ONE_HUNDRED_THIRTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WORD_STAGE_ADMISSION_COMPLETE_ONE_HUNDRED_THIRTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Returned whole canonical field stage success derives original previous typed Open/default absence branch, local key uniqueness, natural capacity, pending source-Ord freshness, optional durable reader success and exact appended original ordered/member field write. No caller admitted result or chosen next object supplied. Branch contracts distinguish capacity and pending refusal before reader and disabled/enabled durable read semantics. Six theorem audits, zero definitions. Reader interface remains fallible native durable query/zip binding; fixed64-bit usize/collections/Scalar/Any/compiler/async/whole delta trace bindings OPEN. Prior pressure attempts retained with zero credit; no accepted ancestor replay/native/control/certification credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("mapping['scope'] += ");end=s.index("mapping_file = ROOT / 'source-mapping.json'",start)
s=s[:start]+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
start=s.index("plan['source_repairs'] += ");end=s.index('\n',start)
s=s[:start]+s[end+1:]
(ROOT/'prepare.py').write_text(s)
print({'returned_source_stage_admission':True,'reports':6,'guards_unchanged':True})
