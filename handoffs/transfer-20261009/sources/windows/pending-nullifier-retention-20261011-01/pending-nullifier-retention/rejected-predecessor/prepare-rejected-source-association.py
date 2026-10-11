"""Derive source object footprints and whole retained nullifier encoding."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-whole-nullifier-admission-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-deferred-body-failure-20261011-03'", "UPSTREAM = DIAG / 'transfer-whole-nullifier-admission-20261011-01'")
s=s.replace('transfer-whole-nullifier-admission-owned-floor-20261011-01','transfer-pending-nullifier-retention-owned-floor-20261011-01')
replace("MODULE = 'TransferWholeNullifierAdmission01'", "MODULE = 'TransferPendingNullifierRetention01'")
replace("stdout = UPSTREAM / 'runs/01-TransferDeferredBodyFailure01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferWholeNullifierAdmission01/stdout.txt'")
replace("records.append(('TransferDeferredBodyFailure01'", "records.append(('TransferWholeNullifierAdmission01'")
replace("'handwritten/TransferDeferredBodyFailure01.lean', 'project/ShielddSecurity/TransferDeferredBodyFailure01.lean']]", "'handwritten/TransferWholeNullifierAdmission01.lean', 'project/ShielddSecurity/TransferWholeNullifierAdmission01.lean']]")
replace("'imports': ['ShielddSecurity.TransferDeferredBodyFailure01']", "'imports': ['ShielddSecurity.TransferWholeNullifierAdmission01']")
replace('assert len(current) == 4','assert len(current) == 6')
replace('assert len(records) == 32 and len(audits) == 319','assert len(records) == 33 and len(audits) == 325')
replace("'objects': 32", "'objects': 33")
s=s.replace('Complete thirty-two-module first owned root; 319 inherited full reports.', 'Complete thirty-three-module first owned root; 325 inherited full reports.')
replace('assert len(names) == 6','assert len(names) == 11')
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'] + ['Pending-nullifier object key differs from tree, pending-note and pending-volume keys; this is a representation/namespace interface until exact source key projection is joined'],
    'scope': 'SCT insertion, pending payload append, arbitrary note output recurrence and Ordinary volume tail derive preservation of every distinct pending-nullifier object on all returned outcomes. For both complete-Item proof contexts and every index mode, whole successful same-action delivery derives an inspected staged pending value, its exact encoded value visible in the delivered parent, full ordered input append, capacity bound/non-sealed status and durable-reader/current-pending freshness of every nonempty projected input. Later callback success, object frame/retention, admitted pending or desired poststate are not caller premises. Nonempty input, capacity below word limit and three object-key inequalities are explicit source representation parameters. Actual object encoding/getter/reader/token/proof/key/byte/ownership/tree/native/Host/durability correspondence and full Transfer certification remain open. Visible pending state is not durable nullifier publication. No new native or negative-control credit.'}
""".rstrip()+s[end:]
s=s.replace('WHOLE_TRANSFER_DELIVERY_DERIVES_ALL_INPUT_NULLIFIER_ADMISSION','WHOLE_TRANSFER_DELIVERY_RETAINS_ADMITTED_PENDING_NULLIFIER_ENCODING')
s=s.replace('WHOLE_NULLIFIER_ADMISSION_COMPLETE_THIRTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','PENDING_NULLIFIER_RETENTION_COMPLETE_THIRTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 6, 'inherited_audits': 319", "'fresh_audits': 11, 'inherited_audits': 325")
s=s.replace('complete thirty-two-module owned root','complete thirty-three-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite symbolic object-footprint/body/index retention composition for both contexts/every index mode; qualified ancestors and guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':11,'inherited_audits':325,'owned_modules':33})
