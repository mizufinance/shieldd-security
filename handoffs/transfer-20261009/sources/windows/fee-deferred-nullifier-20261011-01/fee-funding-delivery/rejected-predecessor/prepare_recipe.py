"""Derive a fresh FeeFunding whole-delivery plan without changing guards."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-deferred-max-count-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-deferred-count-flush-20261011-02'", "UPSTREAM = DIAG / 'transfer-deferred-max-count-20261011-01'")
s=s.replace('transfer-deferred-max-count-owned-floor-20261011-01','transfer-fee-funding-delivery-owned-floor-20261011-01')
replace("MODULE = 'TransferDeferredMaxCount01'", "MODULE = 'TransferFeeFundingDelivery01'")
s=s.replace('TransferDeferredCountFlush01','TransferDeferredMaxCount01')
replace('assert len(records) == 29 and len(audits) == 308','assert len(records) == 30 and len(audits) == 311')
replace("'objects': 29", "'objects': 30")
s=s.replace('Complete twenty-nine-module first owned root; 308 inherited full reports.', 'Complete thirty-module first owned root; 311 inherited full reports.')
replace('assert len(names) == 3', 'assert len(names) == 4')
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'FeeFunding same-action complete Verification re-extraction precedes the installed nullifier/note/SCT program and skips the Ordinary volume tail. All returned outcomes preserve V/NV input writes. Whole per-transaction success derives registry/exclusivity, exact FeeFunding re-extraction, actual transaction conversion, original-parent ID absence/count observation, checked increment, concrete decodable u64 index values, original verifiable state, retained modeled body object/event effects and unchanged deferred queue. It assumes neither Ordinary volume freshness nor callback success, codec roundtrip, frame or desired poststate. Source extraction/token/proof/crypto/key/byte/ownership/native/Host/durability correspondence and full Transfer certification remain open. No new native or negative-control credit.'}
""".rstrip()+s[end:]
s=s.replace('EXACT_MAX_COUNT_DERIVES_DEFERRED_FAILURE_QUEUE_DRAIN_AND_EMPTY_RETRY','FEE_FUNDING_WHOLE_DELIVERY_DERIVES_REEXTRACTION_CURRENT_READS_CODEC_AND_EFFECTS')
s=s.replace('DEFERRED_MAX_COUNT_COMPLETE_TWENTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','FEE_FUNDING_DELIVERY_COMPLETE_THIRTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 3, 'inherited_audits': 308", "'fresh_audits': 4, 'inherited_audits': 311")
s=s.replace('complete twenty-nine-module owned root','complete thirty-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite FeeFunding source/body/whole-delivery composition; inherited proofs and guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':4,'inherited_audits':311,'owned_modules':30})
