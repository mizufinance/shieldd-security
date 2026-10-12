from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-checked-word-stage-refinement-20261011-04/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-stage-numeric-refinement-20261011-03'","UPSTREAM = DIAG / 'transfer-checked-word-stage-refinement-20261011-04'"),
 ("POOL = DIAG / 'transfer-checked-word-stage-refinement-owned-floor-20261011-04'","POOL = DIAG / 'transfer-word-stage-cache-publication-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCheckedWordStageRefinement01'","MODULE = 'TransferWordStageCachePublication01'"),
 ('len(records) == 133 and len(audits) == 1113','len(records) == 134 and len(audits) == 1121'),
 ("'objects': 133","'objects': 134"),
 ('len(names) == 8','len(names) == 4'),
 ('assert len(current) == 6','assert len(current) == 8'),
 ("'imports': ['ShielddSecurity.TransferWordStageNumericRefinement01']","'imports': ['ShielddSecurity.TransferCheckedWordStageRefinement01']"),
 ("'fresh_audits': 8, 'inherited_audits': 1113","'fresh_audits': 4, 'inherited_audits': 1121")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordStageNumericRefinement01','TransferCheckedWordStageRefinement01')+s[end:]
s=s.replace('one-hundred-thirty-three-module','one-hundred-thirty-four-module').replace('1113 inherited full reports','1121 inherited full reports').replace('CHECKED_WORD_STAGE_REFINEMENT_COMPLETE_ONE_HUNDRED_THIRTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WORD_STAGE_CACHE_PUBLICATION_COMPLETE_ONE_HUNDRED_THIRTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Returned checked source stage at actual live functional parent/leaf selected slot derives exact original canonical word field append, one cached object write, next checked getter and all other-key frames, plus successful checked numeric stage at actual previous slot. Modeled durable reader captures actual selected previous pending membership; no caller expected previous value, desired cache, codec inverse, supported-domain, getter-success or field-frame premise. One definition/three theorem audits. Functional views are live model inputs; native applied cache/layers/Any/Clone/imbl/reader/Scalar/usize/compiler/ownership/async/full source trace correspondence remains OPEN. All prior failures and metadata histories retained zero credit; no accepted ancestor replay/native/control/certification credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("mapping['scope'] += ");end=s.index("mapping_file = ROOT / 'source-mapping.json'",start)
s=s[:start]+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s='\n'.join(line for line in s.split('\n') if not line.startswith("plan['source_repairs'] += "))
(ROOT/'prepare.py').write_text(s)
print({'checked_source_single_cached_publication':True,'reports':4,'guards_unchanged':True})
