"""Prepare Host seal phase, actual store observation and same frozen input join."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-host-end-block-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-host-sealed-commit-20261011-04'", "UPSTREAM = DIAG / 'transfer-host-end-block-20261011-01'")
replace("POOL = DIAG / 'transfer-host-end-block-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-host-seal-owned-floor-20261011-01'")
replace("MODULE = 'TransferHostEndBlock01'", "MODULE = 'TransferHostSeal01'")
replace("stdout = UPSTREAM / 'runs/01-TransferHostSealedCommit01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferHostEndBlock01/stdout.txt'")
replace("records.append(('TransferHostSealedCommit01'", "records.append(('TransferHostEndBlock01'")
replace("\n    'handwritten/TransferHostSealedCommit01.lean', 'project/ShielddSecurity/TransferHostSealedCommit01.lean'", "\n    'handwritten/TransferHostEndBlock01.lean', 'project/ShielddSecurity/TransferHostEndBlock01.lean'")
replace('assert len(current) == 12','assert len(current) == 10')
replace('assert len(records) == 65 and len(audits) == 653','assert len(records) == 66 and len(audits) == 663')
replace("'objects': 65", "'objects': 66")
s=s.replace('Complete sixty-five-module first owned root; 653 inherited full reports;', 'Complete sixty-six-module first owned root; 663 inherited full reports;')
replace('assert len(names) == 10','assert len(names) == 7')
replace("'imports': ['ShielddSecurity.TransferHostSealedCommit01']", "'imports': ['ShielddSecurity.TransferHostEndBlock01']")
start=s.index('\nmapping = ')+1;end=s.index('\nmapping_file =',start)
scope='Actual source Host seal_commit EndedBlock-to-CommitInterrupted precedes source writer seal. Returned actual seal derives SealedBlock, original Prepared-to-Sealed same Frozen, actual write lock/intent success and exact independently observed Store after native seal; no ready/roots/current healthy/durability desired poststate inferred. Join actual Host end_block then seal proves same exact transferred pending ordered inputs and same prepared/sealed next boundary. Seven reports (three data/program definitions, four proofs). Source native after-call physical Store/poison observation, finite typed Frozen/Clone/Host phase ownership/locks/filesystem/serde/OS durability correspondence remain interfaces. Formal refusal and source callback success are not executed semantic controls. Zero native/control/full certification.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Host source seal wraps actual source writer seal and threads independently observed Store after that returned call. The observation is a ghost, not a native added read, and no desired ready/roots/healthy outcome is supplied. Native exact Store field/physical observation/locks/filesystem/Clone/owner correspondence remains explicit. Actual end_block-to-seal join preserves the same Frozen and exact ordered inputs from actual transferred pending object, not a silently assumed earlier whole-delivery vector.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_HOST_END_BLOCK_ACTUAL_FINALIZED_TRANSFER_PENDING_VECTOR_AND_PREPARED_OWNER','SOURCE_HOST_SEAL_INTERRUPTION_ACTUAL_INTENT_SAME_FROZEN_AND_OBSERVED_STORE')
s=s.replace('HOST_END_BLOCK_COMPLETE_SIXTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','HOST_SEAL_COMPLETE_SIXTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 10, 'inherited_audits': 653", "'fresh_audits': 7, 'inherited_audits': 663")
s=s.replace('complete sixty-five-module owned root','complete sixty-six-module owned root')
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh Host source seal with actual writer and independent physical Store observation; joins actual end_block pending sequence without desired roots/healthy/durability. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_audits':663,'owned_modules':66})
