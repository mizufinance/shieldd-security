"""Prepare actual participant-to-recovery temporal state threading."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-stateful-store-commit-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-record-read-bound-20261011-01'", "UPSTREAM = DIAG / 'transfer-stateful-store-commit-20261011-02'")
replace("POOL = DIAG / 'transfer-stateful-store-commit-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-stateful-participant-recovery-owned-floor-20261011-01'")
replace("MODULE = 'TransferStatefulStoreCommit01'", "MODULE = 'TransferStatefulParticipantRecovery01'")
replace("stdout = UPSTREAM / 'runs/01-TransferRecordReadBound01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferStatefulStoreCommit01/stdout.txt'")
replace("records.append(('TransferRecordReadBound01'", "records.append(('TransferStatefulStoreCommit01'")
replace("'generated/TransferRecordReadBound01.lean', 'project/ShielddSecurity/TransferRecordReadBound01.lean'", "'handwritten/TransferStatefulStoreCommit01.lean', 'project/ShielddSecurity/TransferStatefulStoreCommit01.lean'")
replace('assert len(current) == 8','assert len(current) == 13')
replace('assert len(records) == 60 and len(audits) == 592','assert len(records) == 61 and len(audits) == 605')
replace("'objects': 60", "'objects': 61")
s=s.replace('Complete sixty-module first owned root; 592 inherited full reports;', 'Complete sixty-one-module first owned root; 605 inherited full reports;')
replace('assert len(names) == 13','assert len(names) == 17')
replace("'imports': ['ShielddSecurity.TransferRecordReadBound01']", "'imports': ['ShielddSecurity.TransferStatefulStoreCommit01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Source participant/writer order threads actual stateful nullifier commit output into actual application commit physical observation, then completion lock physical observation, then exactly that observed Store into original recovery with current-state-indexed independent IO/intent/history observations. Original recovery imported once, not replayed. Seventeen reports (thirteen data/program definitions, four proofs) derive all actual prior gates and recovery/ready/roots/boundary/history/current observed health from participant return; failed nullifier commit and actual application root mismatch retain respective progress and suppress suffix; capacity failure follows Ready with exact completed physical store. Ghost physical observations add no native calls and frame owned ready/boundary, not healthy assumptions or desired recovery state. Native NOMT captured-initial recovery root checks/partition frames, temporal ghost refinement/locks/ownership/library embeddings/Host/storage/ICS23/serde and physical durability remain correspondence interfaces. Zero native/control/full certification.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Source stateful participant pipeline uses actual nullifier commit output as application input and its observed physical roots/current poison health as completion lock input. Actual completion lock observation yields exact recovery invocation Store; no externally supplied desired Store. Recovery IO and intent/history observed callbacks are indexed by that current invocation Store. Native ghost snapshot/lock/store refinement and original captured-initial-root recovery partition frames remain interfaces; model does not certify native temporal correspondence or infer healthy/durable from returned success.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_STATEFUL_STORE_COMMIT_OBSERVED_ROOTS_CURRENT_POISON_AND_OWNED_FRAMES','SOURCE_STATEFUL_PARTICIPANT_APPLICATION_COMPLETION_RECOVERY_INPUT_CHAIN')
s=s.replace('STATEFUL_STORE_COMMIT_COMPLETE_SIXTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','STATEFUL_PARTICIPANT_RECOVERY_COMPLETE_SIXTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 13, 'inherited_audits': 592", "'fresh_audits': 17, 'inherited_audits': 605")
s=s.replace('complete sixty-module owned root','complete sixty-one-module owned root')
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh handwritten actual temporal participant-to-recovery state threading; original recovery reused once. No desired Store/healthy/durability or native correspondence premise silently discharged. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':17,'inherited_audits':605,'owned_modules':61})
