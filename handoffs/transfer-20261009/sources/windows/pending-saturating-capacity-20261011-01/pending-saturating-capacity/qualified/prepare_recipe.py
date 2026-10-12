from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-checked-word-publication-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-word-object-read-20261011-03'","UPSTREAM = DIAG / 'transfer-checked-word-publication-20261011-01'"),
 ("POOL = DIAG / 'transfer-checked-word-publication-owned-floor-20261011-01'","POOL = DIAG / 'transfer-pending-saturating-capacity-owned-floor-20261011-01'"),
 ("MODULE = 'TransferCheckedWordPublication01'","MODULE = 'TransferPendingSaturatingCapacity01'"),
 ('len(current) == 8','len(current) == 2'),
 ('len(records) == 121 and len(audits) == 1044','len(records) == 122 and len(audits) == 1046'),
 ("'objects': 121","'objects': 122"),
 ('len(names) == 2','len(names) == 5'),
 ("'imports': ['ShielddSecurity.TransferWordObjectRead01']","'imports': ['ShielddSecurity.TransferCheckedWordPublication01']"),
 ("'fresh_audits': 2, 'inherited_audits': 1044","'fresh_audits': 5, 'inherited_audits': 1046"),
 ('CHECKED_WORD_PUBLICATION_COMPLETE_ONE_HUNDRED_TWENTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SATURATING_CAPACITY_COMPLETE_ONE_HUNDRED_TWENTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')]:replace(a,b)
start=s.index('stdout = UPSTREAM / ');end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferWordObjectRead01','TransferCheckedWordPublication01')+s[end:]
s=s.replace('one-hundred-twenty-one-module','one-hundred-twenty-two-module').replace('1044 inherited full reports','1046 inherited full reports')
scope=('Pending source capacity comparison uses saturating vector length addition. A finite-width model proves saturation-ceiling headroom makes accepted gate equivalent to exact natural sum bound; closed consensus capacity headroom certified for both 32 and64-bit widths. Accepted gate derives each length bound, so overflow/saturation cannot admit excessive source-model lengths. Five reports, one definition/four theorems. This is a source arithmetic model only: native usize ABI/saturating_add/operator/imbl/vector length/compiler correspondence remain separate. No ancestor replay/native/control/certification credit; full Transfer OPEN.')
start=s.index('\nmapping = ');end=s.index("\nmapping['checked_pending_read_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\nmapping['saturating_capacity_source_shape']=pin(ROOT/'context/saturating-capacity-shape.json')"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"plan['pins'].append(mapping['saturating_capacity_source_shape'])\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
(ROOT/'context').mkdir()
p=Path('C:/src/shieldd-pr160-844389ee/crates/core/component/sct/src/component/tree.rs');b=p.read_bytes();src=b.decode()
body=src[src.index('async fn stage_nullifiers'):src.index('pub const SCT_BLOCK_COMMITMENT_CAPACITY')]
assert 'ordered.len().saturating_add(nullifiers.len()) <= MAX_NULLIFIERS_PER_BLOCK' in body
assert 'pub const MAX_NULLIFIERS_PER_BLOCK: usize = 32_768;' in src
context={'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','runtime_source':{'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()},'source_consensus_limit':'pub const MAX_NULLIFIERS_PER_BLOCK: usize = 32_768;','source_stage_body':body,'scope':'Exact static pinned source comparison and consensus literal only. Model min(sum,2^bits-1) saturation and both32/64 capacity headroom proofs; no native usize ABI/operator/collection/compiler semantics inferred from source identity.'}
(ROOT/'context/saturating-capacity-shape.json').write_text(json.dumps(context,indent=2,sort_keys=True)+'\n')
print({'pending_capacity_source_model':True,'reports':5,'guards_unchanged':True})
