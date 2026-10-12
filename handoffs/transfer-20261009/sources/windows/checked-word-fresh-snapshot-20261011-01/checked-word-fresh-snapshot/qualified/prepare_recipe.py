from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-checked-word-known-finalization-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-checked-word-block-driver-20261011-03'","UPSTREAM = DIAG / 'transfer-checked-word-known-finalization-20261011-01'"),
 ("POOL = DIAG / 'transfer-checked-word-known-finalization-owned-floor-20261011-01'","POOL = DIAG / 'transfer-checked-word-fresh-snapshot-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCheckedWordKnownFinalization01'","MODULE = 'TransferCheckedWordFreshSnapshot01'"),
 ('len(records) == 141 and len(audits) == 1153','len(records) == 142 and len(audits) == 1158'),
 ("'objects': 141","'objects': 142"),
 ("'imports': ['ShielddSecurity.TransferCheckedWordBlockDriver01']","'imports': ['ShielddSecurity.TransferCheckedWordKnownFinalization01']"),
 ("'fresh_audits': 5, 'inherited_audits': 1153","'fresh_audits': 5, 'inherited_audits': 1158")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCheckedWordBlockDriver01','TransferCheckedWordKnownFinalization01')+s[end:]
s=s.replace('one-hundred-forty-one-module','one-hundred-forty-two-module').replace('1153 inherited full reports','1158 inherited full reports').replace('CHECKED_WORD_KNOWN_FINALIZATION_COMPLETE_ONE_HUNDRED_FORTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_FRESH_SNAPSHOT_COMPLETE_ONE_HUNDRED_FORTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Source-shaped Snapshot ephemeral object_get/object_type None and StateDelta new no layers/live default empty leaf instantiate fresh object views. Derives checked absence/default/ordered empty/false sealed/ensure success; complete checked-word public walk and seal returns exact global original field getter, Nodup/capacity/durable false lookup/other-key frames with only whole-run returned success, no caller initial absence or invariant/getter/domain/codec premise. Three definition/two theorem audits. Persistent data/reader remains supplied in backend/child; no durable Snapshot/ICS23 property asserted. Static constructor associations do not establish native semantics; locks/default BTreeMap/Any/constructor caller/compiler/ownership/full trace bindings OPEN; no native/control/replay/certification credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
extra="for row in json.loads((ROOT/'context/source-fresh-snapshot-shape.json').read_bytes())['runtime_sources']:\n    assert row['path'] not in runtime_rows or runtime_rows[row['path']]==row\n    runtime_rows[row['path']]=row\n"
s=s[:start]+"\n"+extra+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
at=s.index("mapping_file = ROOT / 'source-mapping.json'")
s=s[:at]+"mapping['fresh_snapshot_source_shape']=pin(ROOT/'context/source-fresh-snapshot-shape.json')\n"+s[at:]
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"plan['pins'].append(mapping['fresh_snapshot_source_shape'])\n"+s[at:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
runtime=Path('C:/src/shieldd-pr160-844389ee/third_party/cnidarium-0.83.0/src')
def pin(p):
    b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
snapshot=(runtime/'snapshot.rs').read_text();delta=(runtime/'delta.rs').read_text();cache=(runtime/'cache.rs').read_text()
start=snapshot.index('    fn object_get<T: Any + Send + Sync + Clone>');end=snapshot.index('\n}',start)
snapshotExcerpt=snapshot[start:end]
assert snapshotExcerpt.count('None')==2 and 'fn object_type' in snapshotExcerpt
start=delta.index('    pub fn new(state: S) -> Self {');end=delta.index('\n    /// Fork execution',start)
deltaExcerpt=delta[start:end]
assert 'layers: Vec::default()' in deltaExcerpt and 'leaf_cache: Arc::new(RwLock::new(Some(Cache::default())))' in deltaExcerpt
assert '#[derive(Default, Debug)]' in cache and 'ephemeral_objects: BTreeMap' in cache
(ROOT/'context').mkdir()
(ROOT/'context/source-fresh-snapshot-shape.json').write_text(json.dumps({'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','runtime_sources':[pin(runtime/n) for n in ['snapshot.rs','delta.rs','cache.rs']],'snapshot_object_body':snapshotExcerpt,'state_delta_new_body':deltaExcerpt,'cache_default_decl':cache[cache.index('#[derive(Default, Debug)]'):cache.index('\nimpl Cache')],'scope':'Exact static source identities and constructor/read shape. Native default-map/locks/constructor/caller/compiler semantic correspondence separate; no durable data or ICS23 claim.'},indent=2)+'\n')
(ROOT/'prepare.py').write_text(s)
print({'source_shaped_fresh_snapshot_whole_driver':True,'reports':5,'guards_unchanged':True})
