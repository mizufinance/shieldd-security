from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-checked-word-seal-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-stage-cache-publication-20261011-03'","UPSTREAM = DIAG / 'transfer-checked-word-seal-20261011-03'"),
 ("POOL = DIAG / 'transfer-checked-word-seal-owned-floor-20261011-03'","POOL = DIAG / 'transfer-checked-word-seal-publication-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCheckedWordSeal01'","MODULE = 'TransferCheckedWordSealPublication01'"),
 ('len(records) == 135 and len(audits) == 1125','len(records) == 136 and len(audits) == 1133'),
 ("'objects': 135","'objects': 136"),('len(names) == 8','len(names) == 3'),
 ('assert len(current) == 4','assert len(current) == 8'),
 ("'imports': ['ShielddSecurity.TransferWordStageCachePublication01']","'imports': ['ShielddSecurity.TransferCheckedWordSeal01']"),
 ("'fresh_audits': 8, 'inherited_audits': 1125","'fresh_audits': 3, 'inherited_audits': 1133"),
 ("pin(ROOT/'context/checked-word-seal-shape.json')","pin(DIAG/'transfer-checked-word-seal-20261011-03/context/checked-word-seal-shape.json')"),
 ("pin(ROOT/'rejected-object-identity.json')","pin(DIAG/'transfer-checked-word-seal-20261011-03/rejected-object-identity.json')")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordStageCachePublication01','TransferCheckedWordSeal01')+s[end:]
s=s.replace('one-hundred-thirty-five-module','one-hundred-thirty-six-module').replace('1125 inherited full reports','1133 inherited full reports').replace('CHECKED_WORD_SEAL_COMPLETE_ONE_HUNDRED_THIRTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_SEAL_PUBLICATION_COMPLETE_ONE_HUNDRED_THIRTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Returned checked source cache seal derives exact selected Sealed object with original canonical ordered fields, all three actual SCT getters, every other-key frame, and returned stage-then-seal exact fields and capacity. No expected cache, getter/type-domain success, desired codec inverse or prior shape supplied. Three theorem audits. Functional live cache/Any/Clone/imbl/Scalar/reader/compiler/ownership/async/full native trace bindings OPEN. All failed originals and metadata history retained zero credit; no native/control/replay/certification credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'actual_sealed_cache_getters':True,'reports':3,'guards_unchanged':True})
