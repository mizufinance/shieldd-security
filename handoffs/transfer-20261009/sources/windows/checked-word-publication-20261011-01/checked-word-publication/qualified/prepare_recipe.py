from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-word-object-read-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-source-driver-20261011-03'","UPSTREAM = DIAG / 'transfer-word-object-read-20261011-03'"),
 ("POOL = DIAG / 'transfer-word-object-read-owned-floor-20261011-03'","POOL = DIAG / 'transfer-checked-word-publication-owned-floor-20261011-01'"),
 ("MODULE = 'TransferWordObjectRead01'","MODULE = 'TransferCheckedWordPublication01'"),
 ('len(current) == 5','len(current) == 8'),
 ('len(records) == 120 and len(audits) == 1036','len(records) == 121 and len(audits) == 1044'),
 ("'objects': 120","'objects': 121"),
 ('len(names) == 8','len(names) == 2'),
 ("'imports': ['ShielddSecurity.TransferWordSourceDriver01']","'imports': ['ShielddSecurity.TransferWordObjectRead01']"),
 ("'fresh_audits': 8, 'inherited_audits': 1036","'fresh_audits': 2, 'inherited_audits': 1044"),
 ('WORD_OBJECT_READ_COMPLETE_ONE_HUNDRED_TWENTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_PUBLICATION_COMPLETE_ONE_HUNDRED_TWENTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordSourceDriver01','TransferWordObjectRead01')+s[end:]
s=s.replace('one-hundred-twenty-module','one-hundred-twenty-one-module').replace('1036 inherited full reports','1044 inherited full reports')
scope=('Returned whole typed word-field driver derives successful checked native-entry getter on the actual transferred state and exact ordered global mathematical input vector, pending word object, frozen accepted insertions and Ready/Idle application/physical committed boundary. Supported domain, object type and getter success follow from successful walk/publication; no caller final-object/walk/current-state/codec/getter/domain/key-injection correspondence premise. The older extended ghost carrier is a checked panic sentinel, never defaulted. Two reports: one definition and one whole theorem. Known source-ordered finalization only; full native callee/value/trace/imbl/Any/downcast/Clone/private Scalar/compiler/primitive/Choice/CtOption/ownership/snapshot/ICS23/OS semantics remain explicit; no global native ghost erasure. No ancestor replay/native/control/certification credit; full Transfer OPEN.')
start=s.index('\nmapping = ');end=s.index("\nmapping['checked_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
replace("mapping['checked_pending_read_source_shape'] = pin(ROOT/'context/checked-pending-read-shape.json')", "mapping['checked_pending_read_source_shape'] = pin(DIAG/'transfer-word-object-read-20261011-03/context/checked-pending-read-shape.json')")
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'whole_checked_word_publication':True,'reports':2,'guards_unchanged':True})
