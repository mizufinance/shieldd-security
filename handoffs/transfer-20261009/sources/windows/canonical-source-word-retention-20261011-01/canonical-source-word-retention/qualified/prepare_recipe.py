from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-word-sct-pending-read-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-object-put-20261011-03'","UPSTREAM = DIAG / 'transfer-word-sct-pending-read-20261011-01'"),
 ("POOL = DIAG / 'transfer-word-sct-pending-read-owned-floor-20261011-01'","POOL = DIAG / 'transfer-canonical-source-word-retention-owned-floor-20261011-01'"),
 ("MODULE = 'TransferWordSctPendingRead01'","MODULE = 'TransferCanonicalSourceWordRetention01'"),
 ('len(records) == 126 and len(audits) == 1071','len(records) == 127 and len(audits) == 1079'),
 ("'objects': 126","'objects': 127"),
 ('len(names) == 8','len(names) == 3'),
 ("'imports': ['ShielddSecurity.TransferWordObjectPut01']","'imports': ['ShielddSecurity.TransferWordSctPendingRead01']"),
 ("'fresh_audits': 8, 'inherited_audits': 1071","'fresh_audits': 3, 'inherited_audits': 1079"),
 ('SCT_PENDING_WORD_READ_COMPLETE_ONE_HUNDRED_TWENTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CANONICAL_SOURCE_WORD_RETENTION_COMPLETE_ONE_HUNDRED_TWENTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordObjectPut01','TransferWordSctPendingRead01')+s[end:]
s=s.replace('one-hundred-twenty-six-module','one-hundred-twenty-seven-module').replace('1071 inherited full reports','1079 inherited full reports')
scope=('Canonical typed source scalar input retains original raw vector and entire CanonicalScalar when projected to mathematical source key then constructed by LE/parser/choice/R2 word-field codec. Symbolic finite list inverse derives exact original typed fields and order with no caller roundtrip or chosen target output. Packed raw<p invariant is in input type; arbitrary noncanonical raw vectors/aliases receive no identity claim. Three complete theorem audits; local irreducibility only proof-search boundary. Native private Scalar canonical invariant/constructors/selectors/primitive/compiler/imbl/Any/Clone/whole trace correspondence remains separate. No ancestor replay/native/control/certification credit; full Transfer OPEN.')
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
replace("mapping['sct_pending_read_source_shape']=pin(ROOT/'context/sct-pending-read-shape.json')", "mapping['sct_pending_read_source_shape']=pin(DIAG/'transfer-word-sct-pending-read-20261011-01/context/sct-pending-read-shape.json')")
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'canonical_raw_source_field_retention':True,'reports':3,'guards_unchanged':True})
