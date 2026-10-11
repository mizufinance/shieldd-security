"""Prepare checked pending object read, retaining tombstones and type-panic distinction."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
up=DIAG/'transfer-word-source-driver-20261011-03'
s=(up/'prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-object-codec-20261011-01'","UPSTREAM = DIAG / 'transfer-word-source-driver-20261011-03'"),
 ("POOL = DIAG / 'transfer-word-source-driver-owned-floor-20261011-03'","POOL = DIAG / 'transfer-word-object-read-owned-floor-20261011-02'"),
 ("MODULE = 'TransferWordSourceDriver01'","MODULE = 'TransferWordObjectRead01'"),
 ('len(current) == 8','len(current) == 5'),
 ('len(records) == 119 and len(audits) == 1031','len(records) == 120 and len(audits) == 1036'),
 ("'objects': 119","'objects': 120"),
 ('len(names) == 5','len(names) == 8'),
 ("'imports': ['ShielddSecurity.TransferWordObjectCodec01']","'imports': ['ShielddSecurity.TransferWordSourceDriver01']"),
 ("'fresh_audits': 5, 'inherited_audits': 1031","'fresh_audits': 8, 'inherited_audits': 1036"),
 ('WORD_SOURCE_DRIVER_COMPLETE_ONE_HUNDRED_NINETEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WORD_OBJECT_READ_COMPLETE_ONE_HUNDRED_TWENTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordObjectCodec01','TransferWordSourceDriver01')+s[end:]
s=s.replace('one-hundred-nineteen-module','one-hundred-twenty-module').replace('1031 inherited full reports','1036 inherited full reports')
scope=('Checked typed pending object getter model follows source leaf/layer/latest selection and downcast-before-Clone ordering. Absence/tombstone reaches empty default; present wrong type yields an explicit panic sentinel and cannot default/fall through. Successful checked read agrees with the existing projection only on its successful branch; canonical bounded sealed object returns exact finite pending enum from the constructed word codec. Exact cache overlay branch selection preserves these distinctions. Eight reports, three definitions and five theorems. Panic sentinel denotes native non-returning type failure, never recoverable Rust Result or an executed control. Actual Any/TypeId/downcast/Clone/persistent container/lock/compiler semantics and native layers remain independent correspondence obligations. No ancestor replay/native/control/certification credit; full Transfer OPEN.')
start=s.index('\nmapping = ');end=s.index("\nmapping['scalar_decode_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['checked_pending_read_source_shape'] = pin(ROOT/'context/checked-pending-read-shape.json')\n"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"plan['pins'].append(mapping['checked_pending_read_source_shape'])\n"+s[at:]
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"unrunRead=DIAG/'transfer-word-object-read-20261011-01'\nassert not (unrunRead/'events.jsonl').exists()\nplan['pins'] += [pin(unrunRead/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferWordObjectRead01.lean','project/ShielddSecurity/TransferWordObjectRead01.lean','context/checked-pending-read-shape.json']]\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
(ROOT/'context').mkdir()
r=Path('C:/src/shieldd-pr160-844389ee')
paths=['third_party/cnidarium-0.83.0/src/delta.rs','third_party/cnidarium-0.83.0/src/cache.rs','crates/core/component/sct/src/component/tree.rs']
sources=[];snips={}
for path in paths:
    p=r/path;b=p.read_bytes();sources.append({'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()});snips[path]=b.decode()
delta=snips[paths[0]];tree=snips[paths[2]]
get=delta[delta.index('    fn object_get<T:'):delta.index('    fn prefix_raw(',delta.index('    fn object_get<T:'))]
assert get.count('downcast_ref()')==2 and get.count('.cloned()')==2 and 'for layer in self.layers.iter().rev()' in get
assert get.index('leaf_cache')<get.index('for layer')<get.index('self.state')
stage=tree[tree.index('async fn stage_nullifiers'):tree.index('pub const SCT_BLOCK_COMMITMENT_CAPACITY')]
assert stage.index('.object_get::<PendingNullifierBlock>')<stage.index('.unwrap_or_default()')
context={'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','runtime_sources':sources,'object_get_body':get,'pending_stage_body':stage,'scope':'Static source association only. Wrong-type downcast panics before Option absence default. Native Any/Clone/lock/compiler/persistent-container/layers require separate semantic correspondence; no proof/runtime/control credit from source identity.'}
(ROOT/'context/checked-pending-read-shape.json').write_text(json.dumps(context,indent=2,sort_keys=True)+'\n')
(ROOT/'handwritten').mkdir(exist_ok=True)
print({'checked_getter_preparation':True,'reports':8,'guards_unchanged':True})
