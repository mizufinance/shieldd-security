from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-checked-word-fresh-snapshot-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-checked-word-known-finalization-20261011-01'","UPSTREAM = DIAG / 'transfer-checked-word-fresh-snapshot-20261011-01'"),
 ("POOL = DIAG / 'transfer-checked-word-fresh-snapshot-owned-floor-20261011-01'","POOL = DIAG / 'transfer-checked-word-accepted-input-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCheckedWordFreshSnapshot01'","MODULE = 'TransferCheckedWordAcceptedInput01'"),
 ('len(records) == 142 and len(audits) == 1158','len(records) == 143 and len(audits) == 1163'),
 ("'objects': 142","'objects': 143"),('len(names) == 5','len(names) == 4'),
 ("'imports': ['ShielddSecurity.TransferCheckedWordKnownFinalization01']","'imports': ['ShielddSecurity.TransferCheckedWordFreshSnapshot01']"),
 ("'fresh_audits': 5, 'inherited_audits': 1158","'fresh_audits': 4, 'inherited_audits': 1163"),
 ("ROOT/'context/source-fresh-snapshot-shape.json'","DIAG/'transfer-checked-word-fresh-snapshot-20261011-01/context/source-fresh-snapshot-shape.json'")]:replace(a,b,2 if a=="ROOT/'context/source-fresh-snapshot-shape.json'" else 1)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCheckedWordKnownFinalization01','TransferCheckedWordFreshSnapshot01')+s[end:]
s=s.replace('one-hundred-forty-two-module','one-hundred-forty-three-module').replace('1158 inherited full reports','1163 inherited full reports').replace('CHECKED_WORD_FRESH_SNAPSHOT_COMPLETE_ONE_HUNDRED_FORTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_ACCEPTED_INPUT_COMPLETE_ONE_HUNDRED_FORTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Actual getter derived from returned complete fresh snapshot checked-word walk/seal determines ordered accepted source key vector, exact global Montgomery value projection, uniqueness/capacity, every canonical key bound and durable false lookup. Every original typed word field serializes to exactly32 bytes and canonical Montgomery key. One definition/three theorem audits. Host source pending getter then iter/copied/collect/prepare shape is associated statically, not native semantic credit. Native imbl/Vec/iter/copied/collect/Nullifier Copy/private Scalar/reader/ABI/compiler/Host/writer/full trace binding OPEN; all prior failure/metadata histories retained zero credit; no runtime/control/replay/certification credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
at=s.index("mapping_file = ROOT / 'source-mapping.json'")
s=s[:at]+"mapping['checked_word_accepted_source_shape']=pin(ROOT/'context/checked-word-accepted-source-shape.json')\n"+s[at:]
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"plan['pins'].append(mapping['checked_word_accepted_source_shape'])\n"+s[at:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
import json,hashlib
runtime=Path('C:/src/shieldd-pr160-844389ee')
def capture(relative,startMarker,endMarker):
    path=runtime/relative;b=path.read_bytes();text=b.decode();start=text.index(startMarker);end=text.index(endMarker,start)
    return {'source':{'path':str(path),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()},'excerpt':text[start:end]}
getter=capture('crates/core/component/sct/src/component/tree.rs','    fn pending_nullifiers(&self) -> imbl::Vector<Nullifier> {','\n    /// Return whether')
host=capture('crates/core/app/src/app/host.rs','        let accepted = state.pending_nullifiers().iter().copied().collect();','        self.phase = HostExecutionPhase::EndedBlock;')
assert 'pending.ordered().clone()' in getter['excerpt'] and host['excerpt'].count('accepted')==2 and '.prepare(' in host['excerpt']
(ROOT/'context').mkdir()
(ROOT/'context/checked-word-accepted-source-shape.json').write_text(json.dumps({'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','getter':getter,'host':host,'scope':'Exact static getter clone then iter/copied/collect and writer.prepare accepted argument shape; native collection/Copy/ABI/Host/writer/callee correspondence separate.'},indent=2)+'\n')
(ROOT/'prepare.py').write_text(s)
print({'actual_getter_to_accepted_word_projection':True,'reports':4,'guards_unchanged':True})
