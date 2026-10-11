"""Compose actual successful body delivery with derived deferred failure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-fee-funding-delivery-20261011-03/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-deferred-max-count-20261011-01'", "UPSTREAM = DIAG / 'transfer-fee-funding-delivery-20261011-03'")
s=s.replace('transfer-fee-funding-delivery-owned-floor-20261011-03','transfer-deferred-body-failure-owned-floor-20261011-01')
replace("MODULE = 'TransferFeeFundingDelivery01'", "MODULE = 'TransferDeferredBodyFailure01'")
s=s.replace('TransferDeferredMaxCount01','TransferFeeFundingDelivery01')
replace('assert len(current) == 3','assert len(current) == 4')
replace('assert len(records) == 30 and len(audits) == 311','assert len(records) == 31 and len(audits) == 315')
replace("'objects': 30", "'objects': 31")
s=s.replace('Complete thirty-module first owned root; 311 inherited full reports.', 'Complete thirty-one-module first owned root; 315 inherited full reports.')
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Both actual typed ProofContext branches use qualified complete-Item bound Ordinary/FeeFunding source programs. Successful deferred delivery derives body success/re-extraction, successful modeled height read, full parent cache apply, exact body events, queue append of the same action and original NV preservation. Exact max-count bytes are assumed only in the original pre-delivery parent, so derived post-delivery NV and nonempty actual queue imply some deferred index failure, preservation of already-delivered body effects, queue consumption and same-instance empty retry. No failed callback, desired poststate, supplied body cache, supplied nonempty queue or rollback conclusion is assumed. Flush acquisition/known height are explicit phase preconditions; actual height/bytes/keys/token/proof/Rust ownership/Host/native/durability correspondence and full Transfer certification remain open. Earlier errors are not semantic overflow controls. No new native or negative-control credit.'}
""".rstrip()+s[end:]
s=s.replace('FEE_FUNDING_WHOLE_DELIVERY_DERIVES_REEXTRACTION_CURRENT_READS_CODEC_AND_EFFECTS','DEFERRED_BODY_DELIVERY_THEN_MAX_COUNT_FAILURE_DERIVES_EFFECT_PRESERVATION_QUEUE_AND_RETRY')
s=s.replace('FEE_FUNDING_DELIVERY_COMPLETE_THIRTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','DEFERRED_BODY_FAILURE_COMPLETE_THIRTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 4, 'inherited_audits': 311", "'fresh_audits': 4, 'inherited_audits': 315")
s=s.replace('complete thirty-module owned root','complete thirty-one-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite both-context deferred body/index failure/empty retry composition; qualified ancestors and guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':4,'inherited_audits':315,'owned_modules':31})
