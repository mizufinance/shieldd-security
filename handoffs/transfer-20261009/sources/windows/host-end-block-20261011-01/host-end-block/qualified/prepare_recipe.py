"""Prepare actual checked-height Host end_block transfer/prepare chain."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-host-sealed-commit-20261011-04/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-take-commit-state-20261011-02'", "UPSTREAM = DIAG / 'transfer-host-sealed-commit-20261011-04'")
replace("POOL = DIAG / 'transfer-host-sealed-commit-owned-floor-20261011-04'", "POOL = DIAG / 'transfer-host-end-block-owned-floor-20261011-01'")
replace("MODULE = 'TransferHostSealedCommit01'", "MODULE = 'TransferHostEndBlock01'")
replace("stdout = UPSTREAM / 'runs/01-TransferTakeCommitState01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferHostSealedCommit01/stdout.txt'")
replace("records.append(('TransferTakeCommitState01'", "records.append(('TransferHostSealedCommit01'")
replace("\n    'handwritten/TransferTakeCommitState01.lean', 'project/ShielddSecurity/TransferTakeCommitState01.lean'", "\n    'handwritten/TransferHostSealedCommit01.lean', 'project/ShielddSecurity/TransferHostSealedCommit01.lean'")
replace('assert len(current) == 11','assert len(current) == 12')
replace('assert len(records) == 64 and len(audits) == 641','assert len(records) == 65 and len(audits) == 653')
replace("'objects': 64", "'objects': 65")
s=s.replace('Complete sixty-four-module first owned root; 641 inherited full reports;', 'Complete sixty-five-module first owned root; 653 inherited full reports;')
replace('assert len(names) == 12','assert len(names) == 10')
replace("'imports': ['ShielddSecurity.TransferTakeCommitState01']", "'imports': ['ShielddSecurity.TransferHostSealedCommit01']")
start=s.index('\nmapping = ')+1;end=s.index('\nmapping_file =',start)
scope='Host end_block after actual successful checked native i64-to-u64 conversion uses current observed height, actual returned application end_block state/queue/events, concrete take_commit_state and actual block identity before writer.prepare on exact transferred state/current pending ordered vector. Success derives EndedBlock, exact source Prepared owner/boundary and frozen accepted vector from actual calls; height mismatch precedes application/interruption, failed transfer and missing block identity retain interrupted Host and actual transfer progress. Ten reports (six data/program definitions, four proofs). Native checked signed-height domain and application end_block returned observations/component effects/flush/SCT/epoch/Arc expect panics, pending codec/key/Clone/ownership/snapshot/Host temporal/lock correspondence remain interfaces. No desired finalized state or accepted vector is supplied; no callback failure default or physical rollback inferred. Zero native/control/full certification.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Host end_block branch is modeled after successfully checked native i64-to-u64 conversion; supplied Fin64 has actual native signed-height-domain correspondence as an interface. Actual app end_block returned state/queue/events are threaded into concrete state transfer, not desired poststate. Native app deferred-flush/component/seal/epoch/Arc expect panics precede Host interruption and are outside returned-call model. Prepared accepted vector is extracted from the actual transferred current pending object; no silent equality with earlier whole-delivery vector absent native component/pending observation correspondence.'],\n    'scope': "+repr(scope)+"}"+s[end:]
replace("plan['pins'].append(pin(UPSTREAM / 'rejected-object-identity.json'))", "plan['pins'].append(pin(DIAG / 'transfer-take-commit-state-20261011-02/rejected-object-identity.json'))")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
s=s.replace(anchor,"plan['pins'].append(pin(DIAG / 'transfer-capstone-plan-20261011-01/plan.json'))\n"+anchor)
s=s.replace('SOURCE_ORDINARY_HOST_SEALED_COMMIT_INTERRUPTION_ACTUAL_WRITER_AND_RESET','SOURCE_HOST_END_BLOCK_ACTUAL_FINALIZED_TRANSFER_PENDING_VECTOR_AND_PREPARED_OWNER')
s=s.replace('HOST_SEALED_COMMIT_COMPLETE_SIXTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','HOST_END_BLOCK_COMPLETE_SIXTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 12, 'inherited_audits': 641", "'fresh_audits': 10, 'inherited_audits': 653")
s=s.replace('complete sixty-four-module owned root','complete sixty-five-module owned root')
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh actual checked-height Host source end_block state/queue/event transfer and prepared owner composition. All native signed-height/component/ownership/panic/pending correspondence contracts remain explicit. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':10,'inherited_audits':653,'owned_modules':65})
