from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-word-stage-cache-publication-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-checked-word-stage-refinement-20261011-04'","UPSTREAM = DIAG / 'transfer-word-stage-cache-publication-20261011-03'"),
 ("POOL = DIAG / 'transfer-word-stage-cache-publication-owned-floor-20261011-03'","POOL = DIAG / 'transfer-checked-word-seal-owned-floor-20261011-01'"),
 ("MODULE = 'TransferWordStageCachePublication01'","MODULE = 'TransferCheckedWordSeal01'"),
 ('len(records) == 134 and len(audits) == 1121','len(records) == 135 and len(audits) == 1125'),
 ("'objects': 134","'objects': 135"),('len(names) == 4','len(names) == 8'),
 ('assert len(current) == 8','assert len(current) == 4'),
 ("'imports': ['ShielddSecurity.TransferCheckedWordStageRefinement01']","'imports': ['ShielddSecurity.TransferWordStageCachePublication01']"),
 ("'fresh_audits': 4, 'inherited_audits': 1121","'fresh_audits': 8, 'inherited_audits': 1125")]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCheckedWordStageRefinement01','TransferWordStageCachePublication01')+s[end:]
s=s.replace('one-hundred-thirty-four-module','one-hundred-thirty-five-module').replace('1121 inherited full reports','1125 inherited full reports').replace('WORD_STAGE_CACHE_PUBLICATION_COMPLETE_ONE_HUNDRED_THIRTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CHECKED_WORD_SEAL_COMPLETE_ONE_HUNDRED_THIRTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
scope='Checked source seal defaults only absent selected object to empty Open, preserves wrong-type panic and already-Sealed refusal, then checked-put replaces Open with Sealed retaining original ordered canonical fields. Returned cache stage derives exact seal operation and sealed getter observations. Actual prior absent/Open shape derived from returned seal; no supplied type-domain, getter-success, codec inverse or desired output. Two definition/six theorem audits. Native Any/Clone/imbl/Scalar/compiler/ownership/async/cache/reader/full trace bindings OPEN; no native/control/replay/certification credit. All prior failed originals retained zero credit.'
start=s.index('\nmapping = ');end=s.index("\nmapping['sct_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
# Source shape is authenticated independently and remains static association.
at=s.index("mapping_file = ROOT / 'source-mapping.json'")
s=s[:at]+"mapping['checked_word_seal_source_shape']=pin(ROOT/'context/checked-word-seal-shape.json')\n"+s[at:]
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"plan['pins'].append(mapping['checked_word_seal_source_shape'])\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
import hashlib,json
runtime=Path('C:/src/shieldd-pr160-844389ee/crates/core/component/sct/src/component/tree.rs')
b=runtime.read_bytes();text=b.decode()
start=text.index('    async fn seal_nullifier_block(&mut self) -> Result<()> {')
end=text.index('\n    /// Seal the current block',start)
excerpt=text[start:end]
assert excerpt.index('object_get::<PendingNullifierBlock>')<excerpt.index('unwrap_or_default()')<excerpt.index('PendingNullifierBlock::Sealed')<excerpt.index('anyhow::bail!')<excerpt.index('PendingNullifierBlock::Open')<excerpt.index('self.object_put(')<excerpt.index('PendingNullifierBlock::Sealed { ordered }')
(ROOT/'context').mkdir()
(ROOT/'context/checked-word-seal-shape.json').write_text(json.dumps({'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','source':{'path':str(runtime),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()},'excerpt':excerpt,'scope':'Authenticated static call/branch/value shape only; hash does not establish semantic correspondence.'},indent=2)+'\n')
print({'checked_source_seal':True,'reports':8,'guards_unchanged':True})
