"""Prepare exact max-count deferred failure/retry on the qualified closure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-deferred-count-flush-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-deferred-count-walk-20261011-02'", "UPSTREAM = DIAG / 'transfer-deferred-count-flush-20261011-02'")
s=s.replace('transfer-deferred-count-flush-owned-floor-20261011-02','transfer-deferred-max-count-owned-floor-20261011-01')
s=s.replace("MODULE = 'TransferDeferredCountFlush01'", "MODULE = 'TransferDeferredMaxCount01'")
s=s.replace('TransferDeferredCountWalk01','TransferDeferredCountFlush01')
replace('assert len(current) == 4','assert len(current) == 3')
replace('assert len(records) == 28 and len(audits) == 305','assert len(records) == 29 and len(audits) == 308')
replace("'objects': 28", "'objects': 29")
s=s.replace('Complete twenty-eight-module first owned root; 305 inherited full reports.','Complete twenty-nine-module first owned root; 308 inherited full reports.')
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Exact maximal-u64 parent count bytes exclude successful nonempty deferred indexing via the derived arbitrary-list no-wrap bound. For every conversion/read-availability outcome, whole flush after acquisition/height success derives some actual index error, original parent preservation and drained queue; same-instance empty retry cannot reconstruct entries under arbitrary retry callback/exclusive/height. No failed callback, decoder/overflow, desired poststate or rollback premise is supplied. Earlier conversion/duplicate/read errors are not promoted to intended semantic overflow controls. Rust key/byte/ownership/crypto/private-fault/Host/native/durability and full Transfer correspondence remain open. No new native or negative-control credit.'}
""".rstrip()+s[end:]
s=s.replace('WHOLE_DEFERRED_FLUSH_DERIVES_COUNT_QUEUE_AND_NON_INDEX_EFFECT_PRESERVATION','EXACT_MAX_COUNT_DERIVES_DEFERRED_FAILURE_QUEUE_DRAIN_AND_EMPTY_RETRY')
s=s.replace('DEFERRED_COUNT_FLUSH_COMPLETE_TWENTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','DEFERRED_MAX_COUNT_COMPLETE_TWENTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 3, 'inherited_audits': 305", "'fresh_audits': 3, 'inherited_audits': 308")
s=s.replace('complete twenty-eight-module owned root','complete twenty-nine-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite exact max-count deferred failure and same-instance retry composition; all inherited proofs and guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':3,'inherited_audits':308,'owned_modules':29})
