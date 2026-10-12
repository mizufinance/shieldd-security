from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-word-object-put-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-layer-flatten-20261011-03'","UPSTREAM = DIAG / 'transfer-word-object-put-20261011-03'"),
 ("POOL = DIAG / 'transfer-word-object-put-owned-floor-20261011-03'","POOL = DIAG / 'transfer-word-sct-pending-read-owned-floor-20261011-01'"),
 ("MODULE = 'TransferWordObjectPut01'","MODULE = 'TransferWordSctPendingRead01'"),
 ('len(current) == 4','len(current) == 8'),
 ('len(records) == 125 and len(audits) == 1063','len(records) == 126 and len(audits) == 1071'),
 ("'objects': 125","'objects': 126"),
 ("'imports': ['ShielddSecurity.TransferWordLayerFlatten01']","'imports': ['ShielddSecurity.TransferWordObjectPut01']"),
 ("'fresh_audits': 8, 'inherited_audits': 1063","'fresh_audits': 8, 'inherited_audits': 1071"),
 ('CHECKED_WORD_OBJECT_PUT_COMPLETE_ONE_HUNDRED_TWENTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCT_PENDING_WORD_READ_COMPLETE_ONE_HUNDRED_TWENTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordLayerFlatten01','TransferWordObjectPut01')+s[end:]
s=s.replace('one-hundred-twenty-five-module','one-hundred-twenty-six-module').replace('1063 inherited full reports','1071 inherited full reports')
scope=('Source SCT pending ordered/enum sealed/ensure-sealed getters composed with checked typed object read. Typed absence yields empty vector and false isSealed while ensure succeeds; Open retains ordered vector and returns open refusal; Sealed retains ordered vector and returns success. Wrong type produces outer non-returning panic sentinel before any default or returned refusal. Explicit absence witness proves ensure success alone cannot imply present sealed enum. Eight reports, three definitions and five theorems. Outer panic sentinel and inner returned refusal distinct; no executed negative-control credit. Native object downcast/Clone/imbl/Scalar/compiler/ownership/liveness correspondence remains separate; no ancestor replay/native/certification credit; full Transfer OPEN.')
start=s.index('\nmapping = ');end=s.index("\nmapping['checked_pending_put_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['sct_pending_read_source_shape']=pin(ROOT/'context/sct-pending-read-shape.json')"+s[end:]
replace("mapping['checked_pending_put_source_shape']=pin(ROOT/'context/checked-pending-put-shape.json')", "mapping['checked_pending_put_source_shape']=pin(DIAG/'transfer-word-object-put-20261011-03/context/checked-pending-put-shape.json')")
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"plan['pins'].append(mapping['sct_pending_read_source_shape'])\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
(ROOT/'context').mkdir()
p=Path('C:/src/shieldd-pr160-844389ee/crates/core/component/sct/src/component/tree.rs');b=p.read_bytes();src=b.decode()
body=src[src.index('    fn pending_nullifiers('):src.index('impl<T: StateRead + ?Sized> SctRead for T {}')]
enum=src[src.index('pub(super) enum PendingNullifierBlock'):src.index('async fn stage_nullifiers')]
assert '.map(|pending| pending.ordered().clone())' in body and '.unwrap_or_default()' in body
assert 'None | Some(PendingNullifierBlock::Sealed { .. }) => Ok(())' in body
assert 'Some(PendingNullifierBlock::Open { .. })' in body and 'block nullifiers have not been sealed' in body
context={'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','runtime_source':{'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()},'source_pending_enum_and_methods':enum,'source_pending_read_methods':body,'scope':'Exact static source association only. Absence passes ensure-sealed while is-sealed false; wrong-type downcast panics before typed default. Native Any/Clone/imbl/private Scalar/compiler/owner/liveness bindings remain separate; zero native/control/certification credit.'}
(ROOT/'context/sct-pending-read-shape.json').write_text(json.dumps(context,indent=2,sort_keys=True)+'\n')
print({'sct_typed_pending_read_branches':True,'reports':8,'guards_unchanged':True})
