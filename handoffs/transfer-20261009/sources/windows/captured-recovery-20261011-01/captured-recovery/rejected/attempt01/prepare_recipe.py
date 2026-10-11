"""Prepare captured-initial rollback recurrence with explicit native frame contract."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-stateful-participant-recovery-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-stateful-store-commit-20261011-02'", "UPSTREAM = DIAG / 'transfer-stateful-participant-recovery-20261011-01'")
replace("POOL = DIAG / 'transfer-stateful-participant-recovery-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-captured-recovery-owned-floor-20261011-01'")
replace("MODULE = 'TransferStatefulParticipantRecovery01'", "MODULE = 'TransferCapturedRecovery01'")
replace("stdout = UPSTREAM / 'runs/01-TransferStatefulStoreCommit01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferStatefulParticipantRecovery01/stdout.txt'")
replace("records.append(('TransferStatefulStoreCommit01'", "records.append(('TransferStatefulParticipantRecovery01'")
replace("\n    'handwritten/TransferStatefulStoreCommit01.lean', 'project/ShielddSecurity/TransferStatefulStoreCommit01.lean'", "\n    'handwritten/TransferStatefulParticipantRecovery01.lean', 'project/ShielddSecurity/TransferStatefulParticipantRecovery01.lean'")
replace('assert len(current) == 13','assert len(current) == 17')
replace('assert len(records) == 61 and len(audits) == 605','assert len(records) == 62 and len(audits) == 622')
replace("'objects': 61", "'objects': 62")
s=s.replace('Complete sixty-one-module first owned root; 605 inherited full reports;', 'Complete sixty-two-module first owned root; 622 inherited full reports;')
replace('assert len(names) == 17','assert len(names) == 8')
replace("'imports': ['ShielddSecurity.TransferStatefulStoreCommit01']", "'imports': ['ShielddSecurity.TransferStatefulParticipantRecovery01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Exact source rollback selection uses captured initial actual_roots while physical callback outcomes thread current progress. Symbolic recurrence covers all sixteen partitions without unrolling. Explicit ForwardPartitionFrames callback contract preserves later partition observations after successful earlier rollback and is the necessary native NOMT/locking/observation interface for reusing original changing-root recovery; it never forces own-root restoration, success, healthy state or durability. Eight reports (four program/contract definitions, four proofs) establish recurrence equivalence under frames/tail correspondence, failing callback progress/suffix suppression, source prepare and full recovery equality under explicit native frames. Original recovery reports reused once without replay. Independently observed physical root/poison semantics, actual final root read, native partition representation/session isolation/locks, serde/file IO, ownership and source execution correspondence remain interfaces. Zero native/control/full certification.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Captured original actual root vector is used for source rollback selection. Equivalence to original dynamic selection is conditional on explicit ForwardPartitionFrames: successful rollback of index i preserves roots of each later index j. This is a native partition-isolation/current observation contract, not established by a source hash, desired final roots, or a runtime control; it does not demand rollback success/restoration/healthy/durability. Symbolic induction reuses full original recovery result without replay under that contract. Native callback physical snapshot and final actual_roots observation correspondence remain open.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_STATEFUL_PARTICIPANT_APPLICATION_COMPLETION_RECOVERY_INPUT_CHAIN','SOURCE_CAPTURED_INITIAL_RECOVERY_SELECTION_EXPLICIT_FORWARD_PARTITION_FRAME_BRIDGE')
s=s.replace('STATEFUL_PARTICIPANT_RECOVERY_COMPLETE_SIXTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CAPTURED_RECOVERY_COMPLETE_SIXTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 17, 'inherited_audits': 605", "'fresh_audits': 8, 'inherited_audits': 622")
s=s.replace('complete sixty-one-module owned root','complete sixty-two-module owned root')
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh symbolic source captured-initial recurrence and explicitly conditional original recovery bridge. Native frame contract remains a premise. No original recovery replay or native/control/certification credit. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_audits':622,'owned_modules':62})
