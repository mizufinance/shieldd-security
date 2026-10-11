"""Prepare exact max-count refusal on the complete guarded codec-join closure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-ordinary-count-codec-join-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-index-count-codec-20261011-02'", "UPSTREAM = DIAG / 'transfer-ordinary-count-codec-join-20261011-01'")
s=s.replace('transfer-ordinary-count-codec-join-owned-floor-20261011-01','transfer-ordinary-max-count-owned-floor-20261011-01')
s=s.replace("MODULE = 'TransferOrdinaryCountCodecJoin01'", "MODULE = 'TransferOrdinaryMaxCount01'")
s=s.replace('TransferIndexCountCodec01','TransferOrdinaryCountCodecJoin01')
replace('assert len(current) == 15','assert len(current) == 6')
replace("'handwritten/TransferOrdinaryCountCodecJoin01.lean'", "'generated/TransferOrdinaryCountCodecJoin01.lean'")
replace('assert len(records) == 23 and len(audits) == 271','assert len(records) == 24 and len(audits) == 277')
replace("'objects': 23", "'objects': 24")
s=s.replace('Complete twenty-three-module first owned root; 271 inherited full reports.','Complete twenty-four-module first owned root; 277 inherited full reports.')
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Exact eight-byte maximal u64 count: symbolic width recurrence derives big-endian value, concrete codec derives decoded maximum ordinal, and available preceding conversion/absent-ID/current-count reads derive semantic overflow. Whole same-action Ordinary delivery with original stored max bytes refuses for all conversion/extractor/body/read-availability outcomes and enclosing finish preserves parent/queue. No decoder or overflow premise is supplied by the caller. Native Rust/byte/key/proof/token/store/tree/block/durability correspondence remains open. Maintained generator reproduces exact source; no new native or semantic control credit and full Transfer remains open.'}
""".rstrip()+s[end:]
s=s.replace('TYPED_BYTES_CONCRETE_COUNT_CODEC_WHOLE_ORDINARY_REFUSAL','EXACT_MAX_U64_BYTES_DERIVE_SEMANTIC_OVERFLOW_AND_WHOLE_ORDINARY_REFUSAL')
s=s.replace('ORDINARY_COUNT_CODEC_JOIN_COMPLETE_TWENTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','ORDINARY_MAX_COUNT_COMPLETE_TWENTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 6, 'inherited_audits': 271", "'fresh_audits': 6, 'inherited_audits': 277")
s=s.replace('complete twenty-three-module owned root','complete twenty-four-module owned root')
s=s.replace('Fresh generated typed-byte/concrete-codec specialization of qualified whole Ordinary contracts; no predecessor changes or ancestor replays.','Fresh generated exact max-byte/concrete-codec specialization of qualified whole Ordinary contracts; no predecessor changes or ancestor replays.')
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':6,'inherited_audits':277,'owned_modules':24})
