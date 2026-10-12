from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-canonical-source-word-retention-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-sct-pending-read-20261011-01'","UPSTREAM = DIAG / 'transfer-canonical-source-word-retention-20261011-01'"),
 ("POOL = DIAG / 'transfer-canonical-source-word-retention-owned-floor-20261011-01'","POOL = DIAG / 'transfer-canonical-source-publication-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCanonicalSourceWordRetention01'","MODULE = 'TransferCanonicalSourcePublication01'"),
 ('len(records) == 127 and len(audits) == 1079','len(records) == 128 and len(audits) == 1082'),
 ("'objects': 127","'objects': 128"),
 ('len(names) == 3','len(names) == 5'),
 ('assert len(current) == 8','assert len(current) == 3'),
 ("'imports': ['ShielddSecurity.TransferWordSctPendingRead01']","'imports': ['ShielddSecurity.TransferCanonicalSourceWordRetention01']"),
 ("'fresh_audits': 3, 'inherited_audits': 1079","'fresh_audits': 5, 'inherited_audits': 1082")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordSctPendingRead01','TransferCanonicalSourceWordRetention01')+s[end:]
s=s.replace('one-hundred-twenty-seven-module','one-hundred-twenty-eight-module').replace('1079 inherited full reports','1082 inherited full reports').replace('CANONICAL_SOURCE_WORD_RETENTION_COMPLETE_ONE_HUNDRED_TWENTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CANONICAL_SOURCE_PUBLICATION_COMPLETE_ONE_HUNDRED_TWENTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Constructed complete block returned success derives exact original ordered canonical typed source scalar fields in reached Sealed pending object and checked SCT ordered getter, plus unchanged accepted mathematical keys, Ready/Idle, application root and physical roots/boundary. Symbolic installed-input projection and retained field codec derive identity without caller walk/current-state/desired-object/codec-inverse/canonical-bound/frame/getter-success premises. CanonicalScalar input type owns packed raw<p; native private Scalar invariant/selectors, Any/downcast/Clone/imbl/liveness/compiler/full source trace/ownership/OS remain separate and OPEN. Two definitions and three complete theorem audits. No ancestor replay/native/control/certification credit; full Transfer OPEN.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'canonical_original_source_fields_publication':True,'reports':5,'guards_unchanged':True})
