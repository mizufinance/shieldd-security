"""Prepare ordinary sealed Host commit with actual stateful writer and reset."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-take-commit-state-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-captured-recovery-20261011-04'", "UPSTREAM = DIAG / 'transfer-take-commit-state-20261011-02'")
replace("POOL = DIAG / 'transfer-take-commit-state-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-host-sealed-commit-owned-floor-20261011-01'")
replace("MODULE = 'TransferTakeCommitState01'", "MODULE = 'TransferHostSealedCommit01'")
replace("stdout = UPSTREAM / 'runs/01-TransferCapturedRecovery01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferTakeCommitState01/stdout.txt'")
replace("records.append(('TransferCapturedRecovery01'", "records.append(('TransferTakeCommitState01'")
replace("\n    'handwritten/TransferCapturedRecovery01.lean', 'project/ShielddSecurity/TransferCapturedRecovery01.lean'", "\n    'handwritten/TransferTakeCommitState01.lean', 'project/ShielddSecurity/TransferTakeCommitState01.lean'")
replace('assert len(current) == 8','assert len(current) == 11')
replace('assert len(records) == 63 and len(audits) == 630','assert len(records) == 64 and len(audits) == 641')
replace("'objects': 63", "'objects': 64")
s=s.replace('Complete sixty-three-module first owned root; 630 inherited full reports;', 'Complete sixty-four-module first owned root; 641 inherited full reports;')
replace('assert len(names) == 11','assert len(names) == 12')
replace("'imports': ['ShielddSecurity.TransferCapturedRecovery01']", "'imports': ['ShielddSecurity.TransferTakeCommitState01']")
start=s.index('\nmapping = ')+1;end=s.index('\nmapping_file =',start)
scope='Ordinary SealedBlock source Host commit sets CommitInterrupted before actual state-threaded writer commit, retains actual writer/physical progress on returned failure, and on success resets to observed latest snapshot/current reader, clears block identity, sets Idle, then extracts application root. Actual participant success derives root presence, making missing-root final guard unreachable under this source contract; no vacuous missing-root error control credited. Capacity failure demonstrates Host CommitInterrupted with writer Ready and exact completed observed physical state. Twelve reports (six program/data definitions, six proofs). InitializedGenesis preparation/seal and checkpoint genesis are separate branches, not certified here. Native Host/reader/Arc/object key/snapshot/storage reset/typed roots/concurrency/ownership/captured partition frames/library/ICS23/OS durability remain correspondence interfaces. Zero native/control/full certification.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Ordinary Host SealedBlock commit uses actual stateful writer output. Returned capacity error keeps Host interrupted while writer and recovery may already be Ready/committed. Reset snapshot and typed current reader observations are indexed by actual resulting Store. Actual source writer success already guarantees application root Some, so missing-root final extraction guard is not a reachable semantic negative control. Source genesis/init/recovery/rollback/phase/ownership and native reset snapshot/reader/typed library correspondence remain separate interfaces.'],\n    'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['pins'] += [pin(ROOT / 'rejected-object-identity.json')");end=s.index('\n',start)
s=s[:start]+s[end:]
s=s.replace('SOURCE_TAKE_COMMIT_STATE_SEALED_CONCRETE_FLUSH_EXCLUSIVE_TRANSFER_AND_REPLACEMENT','SOURCE_ORDINARY_HOST_SEALED_COMMIT_INTERRUPTION_ACTUAL_WRITER_AND_RESET')
s=s.replace('TAKE_COMMIT_STATE_COMPLETE_SIXTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','HOST_SEALED_COMMIT_COMPLETE_SIXTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 11, 'inherited_audits': 630", "'fresh_audits': 12, 'inherited_audits': 641")
s=s.replace('complete sixty-three-module owned root','complete sixty-four-module owned root')
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh handwritten ordinary Host source commit with actual stateful writer and reset. Source-derived root presence avoids vacuous missing-root error claims. Genesis/native interfaces remain explicit. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':12,'inherited_audits':641,'owned_modules':64})
