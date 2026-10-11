"""Derive whole-action all-input admission on the exact qualified closure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-deferred-body-failure-20261011-03/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-fee-funding-delivery-20261011-03'", "UPSTREAM = DIAG / 'transfer-deferred-body-failure-20261011-03'")
s=s.replace('transfer-deferred-body-failure-owned-floor-20261011-03','transfer-whole-nullifier-admission-owned-floor-20261011-01')
replace("MODULE = 'TransferDeferredBodyFailure01'", "MODULE = 'TransferWholeNullifierAdmission01'")
# Only the successful immediate ancestor references change; rejected history stays original.
replace("stdout = UPSTREAM / 'runs/01-TransferFeeFundingDelivery01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferDeferredBodyFailure01/stdout.txt'")
replace("records.append(('TransferFeeFundingDelivery01'", "records.append(('TransferDeferredBodyFailure01'")
replace("'handwritten/TransferFeeFundingDelivery01.lean', 'project/ShielddSecurity/TransferFeeFundingDelivery01.lean']]", "'handwritten/TransferDeferredBodyFailure01.lean', 'project/ShielddSecurity/TransferDeferredBodyFailure01.lean']]")
replace("'imports': ['ShielddSecurity.TransferFeeFundingDelivery01']", "'imports': ['ShielddSecurity.TransferDeferredBodyFailure01']")
replace('assert len(records) == 31 and len(audits) == 315','assert len(records) == 32 and len(audits) == 319')
replace("'objects': 31", "'objects': 32")
s=s.replace('Complete thirty-one-module first owned root; 315 inherited full reports.', 'Complete thirty-two-module first owned root; 319 inherited full reports.')
replace('assert len(names) == 4','assert len(names) == 6')
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Whole successful delivery in either Ordinary/FeeFunding context and every index mode derives exact complete-Item re-extraction, successful modeled reshape and nonempty nullifier admission from the same action inputs. The actual installed branch retains original source and nullifier backend; source transaction ID, duplicate loop success, inspected pending append, non-sealed bounded staged vector and durable-reader/pending freshness for every projected input follow the source program, with no supplied successful callback, inspection or fresh-input/poststate premise. Nonempty input and capacity below word limit are explicit runtime parameter interfaces. This is admission before later note effects, not final durable nullifier publication. Authenticated reader/source/extractor/token/proof/keys/bytes/ownership/tree/native/Host/durability correspondence and full Transfer certification remain open. No new native or negative-control credit.'}
""".rstrip()+s[end:]
s=s.replace('DEFERRED_BODY_DELIVERY_THEN_MAX_COUNT_FAILURE_DERIVES_EFFECT_PRESERVATION_QUEUE_AND_RETRY','WHOLE_TRANSFER_DELIVERY_DERIVES_ALL_INPUT_NULLIFIER_ADMISSION')
s=s.replace('DEFERRED_BODY_FAILURE_COMPLETE_THIRTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WHOLE_NULLIFIER_ADMISSION_COMPLETE_THIRTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 4, 'inherited_audits': 315", "'fresh_audits': 6, 'inherited_audits': 319")
s=s.replace('complete thirty-one-module owned root','complete thirty-two-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite complete body-to-nullifier admission inverse for both contexts/every index mode; qualified ancestors and guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':6,'inherited_audits':319,'owned_modules':32})
