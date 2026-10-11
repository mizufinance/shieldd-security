"""Prepare exact source sealed/flush/exclusive transfer and replacement state."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-captured-recovery-20261011-04/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-stateful-participant-recovery-20261011-01'", "UPSTREAM = DIAG / 'transfer-captured-recovery-20261011-04'")
replace("POOL = DIAG / 'transfer-captured-recovery-owned-floor-20261011-04'", "POOL = DIAG / 'transfer-take-commit-state-owned-floor-20261011-01'")
replace("MODULE = 'TransferCapturedRecovery01'", "MODULE = 'TransferTakeCommitState01'")
replace("stdout = UPSTREAM / 'runs/01-TransferStatefulParticipantRecovery01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferCapturedRecovery01/stdout.txt'")
replace("records.append(('TransferStatefulParticipantRecovery01'", "records.append(('TransferCapturedRecovery01'")
replace("\n    'handwritten/TransferStatefulParticipantRecovery01.lean', 'project/ShielddSecurity/TransferStatefulParticipantRecovery01.lean'", "\n    'handwritten/TransferCapturedRecovery01.lean', 'project/ShielddSecurity/TransferCapturedRecovery01.lean'")
replace('assert len(current) == 17','assert len(current) == 8')
replace('assert len(records) == 62 and len(audits) == 622','assert len(records) == 63 and len(audits) == 630')
replace("'objects': 62", "'objects': 63")
s=s.replace('Complete sixty-two-module first owned root; 622 inherited full reports;', 'Complete sixty-three-module first owned root; 630 inherited full reports;')
replace('assert len(names) == 8','assert len(names) == 11')
replace("'imports': ['ShielddSecurity.TransferStatefulParticipantRecovery01']", "'imports': ['ShielddSecurity.TransferCapturedRecovery01']")
anchor="for relative in ['crates/core/app/src/app/permanent_writer.rs'"
assert s.count(anchor)==1
s=s.replace(anchor,"for relative in ['crates/core/app/src/app/host.rs', 'crates/core/app/src/app/lifecycle.rs', 'crates/core/app/src/app/permanent_writer.rs'")
start=s.index('\nmapping = ')+1;end=s.index('\nmapping_file =',start)
scope='Source App::take_commit_state uses actual ensureSealed then concrete deferred flush then fresh latest snapshot replacement containing only the current typed reader, followed by independently observed exclusive Arc unwrap success. Success transfers exact post-flush old state; failed unwrap restores that post-flush state/current queue, not pre-flush state. Concrete index failure preserves already delivered parent effects and consumes queued records while refusing transfer. Successful nonempty concrete flush preserves original V/objects, hence pending data, with actual count observation premise. Eleven reports (five data/program definitions, six proofs). Native Arc/try_unwrap exact value/reference/Clone/panic/ownership and snapshot/object key/reader/current view source correspondence remain explicit; no actual native ownership or no-hidden-alias theorem claimed. No native/control/durability/full certification and no semantic-control credit for formal refusals.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Source state transfer uses existing actual ensureSealed model and concrete deferred index flush. Exclusive unwrap branch is actual independently observed returned native ownership result; source model returns exact previous value and restores it on failure, requiring native Arc/Clone/alias/snapshot/object getter semantic correspondence. Replacement snapshot is observed after flush, installs typed reader and empty other disposable objects. Typed key is supplied explicitly; source literal reader key, object any/downcast panics and complete finite library representation remain native interfaces. Concrete flush-derived object/V frames bind pending data without callback desired-poststate premise.'],\n    'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['pins'] += [pin(ROOT / 'rejected-object-identity.json')");end=s.index('\n',start)
s=s[:start]+s[end:]
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
s=s.replace(anchor,"plan['pins'].append(pin(UPSTREAM / 'rejected-object-identity.json'))\n"+anchor)
s=s.replace('SOURCE_CAPTURED_INITIAL_RECOVERY_SELECTION_EXPLICIT_FORWARD_PARTITION_FRAME_BRIDGE','SOURCE_TAKE_COMMIT_STATE_SEALED_CONCRETE_FLUSH_EXCLUSIVE_TRANSFER_AND_REPLACEMENT')
s=s.replace('CAPTURED_RECOVERY_COMPLETE_SIXTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','TAKE_COMMIT_STATE_COMPLETE_SIXTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 8, 'inherited_audits': 622", "'fresh_audits': 11, 'inherited_audits': 630")
s=s.replace('complete sixty-two-module owned root','complete sixty-three-module owned root')
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh handwritten actual source transfer with concrete reused flush proofs. Native ownership/library semantic contracts remain interfaces; no ancestor replay or native/control/certification credit. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':11,'inherited_audits':630,'owned_modules':63})
