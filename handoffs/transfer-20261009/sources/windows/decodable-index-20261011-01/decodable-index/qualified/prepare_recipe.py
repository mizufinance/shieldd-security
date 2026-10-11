"""Prepare a single whole-call concrete-key/value codec success theorem."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-ordinary-max-count-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-ordinary-count-codec-join-20261011-01'", "UPSTREAM = DIAG / 'transfer-ordinary-max-count-20261011-02'")
s=s.replace('transfer-ordinary-max-count-owned-floor-20261011-02','transfer-ordinary-decodable-index-owned-floor-20261011-01')
s=s.replace("MODULE = 'TransferOrdinaryMaxCount01'", "MODULE = 'TransferOrdinaryDecodableIndex01'")
s=s.replace('TransferOrdinaryCountCodecJoin01','TransferOrdinaryMaxCount01')
replace('assert len(records) == 24 and len(audits) == 277','assert len(records) == 25 and len(audits) == 283')
replace("'objects': 24", "'objects': 25")
s=s.replace('Complete twenty-four-module first owned root; 277 inherited full reports.','Complete twenty-five-module first owned root; 283 inherited full reports.')
replace('assert len(names) == 6','assert len(names) == 1')
replace("handwritten = ROOT / 'generated' / (MODULE + '.lean')", "handwritten = ROOT / 'handwritten' / (MODULE + '.lean')")
replace(", ROOT / 'generate.py']", "]")
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Whole same-action Ordinary per-transaction success with actual modeled current NV reads, concrete eight-byte ordinal key encoding and concrete u64 value codec derives exact compared extraction/conversion, checked next ordinal, original volume absence and both marker values, payload/identifier/count writes, eight-byte lengths, valid byte ranges and decoder roundtrips for both stored ordinal values. The same projected source namespaces derive volume key separation. Desired codec, stored-value or successful raw-body postconditions are never caller premises. Rust key prefix/byte projection/ownership/proof/token/crypto/tree/native/block/durability correspondence remains explicit. No new native or semantic control credit; full Transfer remains open.'}
""".rstrip()+s[end:]
s=s.replace('EXACT_MAX_U64_BYTES_DERIVE_SEMANTIC_OVERFLOW_AND_WHOLE_ORDINARY_REFUSAL','WHOLE_ORDINARY_SUCCESS_DERIVES_DECODABLE_CONCRETE_U64_INDEX_VALUES')
s=s.replace('ORDINARY_MAX_COUNT_COMPLETE_TWENTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','ORDINARY_DECODABLE_INDEX_COMPLETE_TWENTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 6, 'inherited_audits': 277", "'fresh_audits': 1, 'inherited_audits': 283")
s=s.replace('complete twenty-four-module owned root','complete twenty-five-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh handwritten whole-call concrete ordinal key/value codec success composition; all inherited proofs and guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':1,'inherited_audits':283,'owned_modules':25})
