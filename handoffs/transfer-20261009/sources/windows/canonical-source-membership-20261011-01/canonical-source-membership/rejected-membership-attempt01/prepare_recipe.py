from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-canonical-source-publication-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-canonical-source-word-retention-20261011-01'","UPSTREAM = DIAG / 'transfer-canonical-source-publication-20261011-01'"),
 ("POOL = DIAG / 'transfer-canonical-source-publication-owned-floor-20261011-01'","POOL = DIAG / 'transfer-canonical-source-membership-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCanonicalSourcePublication01'","MODULE = 'TransferCanonicalSourceMembership01'"),
 ('len(records) == 128 and len(audits) == 1082','len(records) == 129 and len(audits) == 1087'),
 ("'objects': 128","'objects': 129"),
 ('len(names) == 5','len(names) == 6'),
 ('assert len(current) == 3','assert len(current) == 5'),
 ("'imports': ['ShielddSecurity.TransferCanonicalSourceWordRetention01']","'imports': ['ShielddSecurity.TransferCanonicalSourcePublication01']"),
 ("'fresh_audits': 5, 'inherited_audits': 1082","'fresh_audits': 6, 'inherited_audits': 1087")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCanonicalSourceWordRetention01','TransferCanonicalSourcePublication01')+s[end:]
s=s.replace('one-hundred-twenty-eight-module','one-hundred-twenty-nine-module').replace('1082 inherited full reports','1087 inherited full reports').replace('CANONICAL_SOURCE_PUBLICATION_COMPLETE_ONE_HUNDRED_TWENTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CANONICAL_SOURCE_MEMBERSHIP_COMPLETE_ONE_HUNDRED_TWENTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Canonical typed source key globally injective on entire typed fields. Modeled source high-byte-first reversed serializer Ord equality/membership exactly equals source key equality/membership, and key-vector Nodup iff original typed-field Nodup. Returned whole canonical source driver derives original typed-field uniqueness and capacity without extra domain/inverse/desired-state/walk/getter premises. One definition and five theorem audits. Actual Rust BTreeSet/imbl/Ord/PartialEq/iterator/private Scalar invariant/compiler/Any/ownership/whole trace bindings remain separate and OPEN. No ancestor replay/native/control/certification credit; full Transfer OPEN.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'original_source_field_uniqueness_membership':True,'reports':6,'guards_unchanged':True})
