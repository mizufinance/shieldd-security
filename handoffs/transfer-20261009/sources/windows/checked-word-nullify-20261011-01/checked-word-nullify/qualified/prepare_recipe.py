from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-checked-word-seal-publication-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-checked-word-seal-20261011-03'","UPSTREAM = DIAG / 'transfer-checked-word-seal-publication-20261011-02'"),
 ("POOL = DIAG / 'transfer-checked-word-seal-publication-owned-floor-20261011-02'","POOL = DIAG / 'transfer-checked-word-nullify-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCheckedWordSealPublication01'","MODULE = 'TransferCheckedWordNullify01'"),
 ('len(records) == 136 and len(audits) == 1133','len(records) == 137 and len(audits) == 1136'),
 ("'objects': 136","'objects': 137"),('len(names) == 3','len(names) == 6'),
 ('assert len(current) == 8','assert len(current) == 3'),
 ("'imports': ['ShielddSecurity.TransferCheckedWordSeal01']","'imports': ['ShielddSecurity.TransferCheckedWordSealPublication01']"),
 ("'fresh_audits': 3, 'inherited_audits': 1133","'fresh_audits': 6, 'inherited_audits': 1136")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCheckedWordSeal01','TransferCheckedWordSealPublication01')+s[end:]
s=s.replace('one-hundred-thirty-six-module','one-hundred-thirty-seven-module').replace('1133 inherited full reports','1136 inherited full reports').replace('CHECKED_WORD_SEAL_PUBLICATION_COMPLETE_ONE_HUNDRED_THIRTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_NULLIFY_COMPLETE_ONE_HUNDRED_THIRTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Public source nullify_all exact checked word cache operation: empty inputs skip source/type/reader, nonempty missing transaction source refuses before getter, nonempty present source forwards exact checked staging. Returned success derives empty identity or actual nonempty source and checked stage. One definition/five theorem audits. Native source.id selector, functional live cache/Any/Clone/imbl/Scalar/reader/compiler/ownership/async/full trace bindings OPEN; no native/control/replay/certification credit. All prior failed originals and metadata histories retained zero credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'public_nullify_order':True,'reports':6,'guards_unchanged':True})
