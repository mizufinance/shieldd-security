"""Prepare source sealed commit ordering, interruption and post-Ready capacity error."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-writer-seal-discard-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-writer-prepare-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-writer-seal-discard-source-20261011-02'")
replace("POOL = DIAG / 'transfer-writer-seal-discard-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-writer-commit-source-owned-floor-20261011-01'")
replace("MODULE = 'TransferWriterSealDiscardSource01'", "MODULE = 'TransferWriterCommitSource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferWriterPrepareSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferWriterSealDiscardSource01/stdout.txt'")
replace("records.append(('TransferWriterPrepareSource01'", "records.append(('TransferWriterSealDiscardSource01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'repair_recipe.py', 'handwritten/TransferWriterPrepareSource01.lean', 'project/ShielddSecurity/TransferWriterPrepareSource01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'repair_recipe.py', 'handwritten/TransferWriterSealDiscardSource01.lean', 'project/ShielddSecurity/TransferWriterSealDiscardSource01.lean']]")
replace('assert len(current) == 14','assert len(current) == 13')
replace('assert len(records) == 48 and len(audits) == 473','assert len(records) == 49 and len(audits) == 486')
replace("'objects': 48", "'objects': 49")
s=s.replace('Complete forty-eight-module first owned root; 473 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete forty-nine-module first owned root; 486 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 13','assert len(names) == 9')
replace("'imports': ['ShielddSecurity.TransferWriterPrepareSource01']", "'imports': ['ShielddSecurity.TransferWriterSealDiscardSource01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Source PermanentWriter::commit requires Sealed, assigns Interrupted before checking application version/readiness, writer lock, nullifier commit, application batch commit, actual returned root agreement, completion lock and recovery completion. Participant completion derives every prior callback result and independently observed application root equality. Failure before completion leaves owner status unavailable with no physical rollback claim. Completion sets Ready before capacity, so failed capacity retains the new Ready/committed boundary while returning unavailable. Whole returned success derives initial Sealed, completion, capacity, exact frozen boundary and current owner committed value; whole successful prepare/seal/commit retains the exact original frozen accepted inputs and prepared boundary. Nine reports (three data/program definitions, six proofs), finite/physical/strict audit guards unchanged. Native version/Clone/batch/lock/NOMT/session/application/complete/recovery/capacity/owner/durability progress remain explicit callback/refinement interfaces; no native testing/control/full Transfer certification or durable rollback inferred.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Source commit control flow and phase projection only: callbacks denote actual observed results; applicationUnchanged models native wrapping version comparison, and root equality checks the observed commit root. Physical Store roots/partial participant commits, staged batch content, recovery health, lock/Clone/type/owner/async/native correspondence and durable I/O remain interfaces. A capacity error occurs after phase Ready and does not imply rollback or absence of durable progress. Interrupted owner API status is unavailable before its reader callback; raw Store readers require their own proof.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_WRITER_SEAL_DISCARD_COMMITTED_AND_OWNER_STATUS_GATES','SOURCE_WRITER_COMMIT_ORDER_INTERRUPTION_AND_POST_READY_CAPACITY_ERROR')
s=s.replace('WRITER_SEAL_DISCARD_SOURCE_COMPLETE_FORTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WRITER_COMMIT_SOURCE_COMPLETE_FORTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 13, 'inherited_audits': 473", "'fresh_audits': 9, 'inherited_audits': 486")
s=s.replace('complete forty-eight-module owned root','complete forty-nine-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source commit call-order/phase/error proof and same frozen accepted inputs across successful prepare/seal/commit; distinguishes post-Ready capacity error from pre-completion interruption. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':9,'inherited_audits':486,'owned_modules':49})
