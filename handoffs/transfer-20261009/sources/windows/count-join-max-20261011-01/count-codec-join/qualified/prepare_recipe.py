"""Strict generated concrete-codec join on the completed qualified closure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-index-count-codec-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-ordinary-index-count-20261011-01'", "UPSTREAM = DIAG / 'transfer-index-count-codec-20261011-02'")
s=s.replace('transfer-index-count-codec-owned-floor-20261011-02','transfer-ordinary-count-codec-join-owned-floor-20261011-01')
s=s.replace("MODULE = 'TransferIndexCountCodec01'", "MODULE = 'TransferOrdinaryCountCodecJoin01'")
s=s.replace('TransferOrdinaryIndexCountSource01','TransferIndexCountCodec01')
replace('assert len(current) == 6','assert len(current) == 15')
replace('assert len(records) == 22 and len(audits) == 256','assert len(records) == 23 and len(audits) == 271')
replace("'objects': 22", "'objects': 23")
s=s.replace('Complete twenty-two-module first owned root; 256 inherited full reports.','Complete twenty-three-module first owned root; 271 inherited full reports.')
replace('assert len(names) == 15','assert len(names) == 6')
replace("handwritten = ROOT / 'handwritten' / (MODULE + '.lean')", "handwritten = ROOT / 'generated' / (MODULE + '.lean')")
replace('runner, handwritten, target_source, composition_file, mapping_file]', "runner, handwritten, target_source, composition_file, mapping_file, ROOT / 'generate.py']")
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Generated concrete-codec join: mapped Lean UInt8 bytes derive range and length, and exact big-endian codec decoding fails iff byte length differs from eight. Whole same-action Ordinary per-transaction delivery with the concrete codec rejects a stored original-parent count of wrong length; enclosing finish preserves original parent and queue. This uses actual executable body NV framing and source height/key separation, with no body success, desired index error, availability or rollback premise. Rust byte representation/semantics, conversion/height/key/proof/token/store/tree/block/durability remain explicit interfaces. Generated source is reproduced byte-exact from the maintained generator; no new native or semantic control credit and full Transfer remains open.'}
""".rstrip()+s[end:]
s=s.replace('SYMBOLIC_BIG_ENDIAN_U64_INDEX_COUNT_CODEC','TYPED_BYTES_CONCRETE_COUNT_CODEC_WHOLE_ORDINARY_REFUSAL')
s=s.replace('INDEX_COUNT_CODEC_COMPLETE_TWENTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','ORDINARY_COUNT_CODEC_JOIN_COMPLETE_TWENTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 15, 'inherited_audits': 256", "'fresh_audits': 6, 'inherited_audits': 271")
s=s.replace('complete twenty-two-module owned root','complete twenty-three-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh generated typed-byte/concrete-codec specialization of qualified whole Ordinary contracts; no predecessor changes or ancestor replays.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':6,'inherited_audits':271,'owned_modules':23})
