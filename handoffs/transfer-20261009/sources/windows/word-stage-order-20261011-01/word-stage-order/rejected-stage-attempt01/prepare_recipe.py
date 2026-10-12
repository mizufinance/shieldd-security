from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-canonical-source-membership-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-canonical-source-publication-20261011-01'","UPSTREAM = DIAG / 'transfer-canonical-source-membership-20261011-02'"),
 ("POOL = DIAG / 'transfer-canonical-source-membership-owned-floor-20261011-02'","POOL = DIAG / 'transfer-word-stage-order-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCanonicalSourceMembership01'","MODULE = 'TransferWordStageOrder01'"),
 ('len(records) == 129 and len(audits) == 1087','len(records) == 130 and len(audits) == 1093'),
 ("'objects': 129","'objects': 130"),
 ('len(names) == 6','len(names) == 8'),
 ('assert len(current) == 5','assert len(current) == 6'),
 ("'imports': ['ShielddSecurity.TransferCanonicalSourcePublication01']","'imports': ['ShielddSecurity.TransferCanonicalSourceMembership01']"),
 ("'fresh_audits': 6, 'inherited_audits': 1087","'fresh_audits': 8, 'inherited_audits': 1093")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCanonicalSourcePublication01','TransferCanonicalSourceMembership01')+s[end:]
s=s.replace('one-hundred-twenty-nine-module','one-hundred-thirty-module').replace('1087 inherited full reports','1093 inherited full reports').replace('CANONICAL_SOURCE_MEMBERSHIP_COMPLETE_ONE_HUNDRED_TWENTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WORD_STAGE_ORDER_COMPLETE_ONE_HUNDRED_THIRTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Source stage_nullifiers canonical field control order: duplicate rejection before checked typed object read; wrong type non-returning panic distinct from returned sealed/admission refusal; absence default Open; exact original ordered and finite member field append followed by guarded same-type put only after capacity/membership/optional durable interface admission. Local uniqueness uses established source Ord/key equality projection. Fixed64-bit saturation source model; usize ABI/native vector limits remain separate. Reader parameter explicitly owns fallible durable-vector and zip-unspent semantics. Three definitions/five theorem audits. Native Scalar/BTreeSet/imbl/Any/Clone/compiler/async/delta/whole source trace bindings OPEN; no native/control/certification or accepted ancestor replay credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("mapping['scope'] += ");end=s.index("mapping_file = ROOT / 'source-mapping.json'",start)
s=s[:start]+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
start=s.index("plan['source_repairs'] += ");end=s.index('\n',start)
s=s[:start]+s[end+1:]
(ROOT/'prepare.py').write_text(s)
print({'canonical_word_staging_order':True,'reports':8,'guards_unchanged':True})
