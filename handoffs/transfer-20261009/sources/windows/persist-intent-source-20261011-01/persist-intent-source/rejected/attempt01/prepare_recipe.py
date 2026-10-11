"""Prepare source persist-intent idempotence, observed failure progress and read refusal."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-writer-commit-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-writer-seal-discard-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-writer-commit-source-20261011-01'")
replace("POOL = DIAG / 'transfer-writer-commit-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-persist-intent-source-owned-floor-20261011-01'")
replace("MODULE = 'TransferWriterCommitSource01'", "MODULE = 'TransferPersistIntentSource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferWriterSealDiscardSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferWriterCommitSource01/stdout.txt'")
replace("records.append(('TransferWriterSealDiscardSource01'", "records.append(('TransferWriterCommitSource01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'repair_recipe.py', 'handwritten/TransferWriterSealDiscardSource01.lean', 'project/ShielddSecurity/TransferWriterSealDiscardSource01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferWriterCommitSource01.lean', 'project/ShielddSecurity/TransferWriterCommitSource01.lean']]")
replace('assert len(current) == 13','assert len(current) == 9')
replace('assert len(records) == 49 and len(audits) == 486','assert len(records) == 50 and len(audits) == 495')
replace("'objects': 49", "'objects': 50")
s=s.replace('Complete forty-nine-module first owned root; 486 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete fifty-module first owned root; 495 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 9','assert len(names) == 10')
replace("'imports': ['ShielddSecurity.TransferWriterSealDiscardSource01']", "'imports': ['ShielddSecurity.TransferWriterCommitSource01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Source Store::persist_intent readiness/health/current-root/current-boundary guards, fallible serialization, existing-intent observed record equality, next-height/history gates and write failure readiness projection. New intent calls write with ready=false ghost memory state; returned outcome retains exactly the independently observed filesystem state and sets ready from observed returned write success. Existing actual equal intent is idempotent without a new write; unreadable/different existing intent refuses with unchanged modeled Store and filesystem observations. Failed new write retains arbitrary observed filesystem progress, returns failure, leaves modeled Store interrupted and derives status unavailability through original Readback ready gate. Ten reports (six data/program definitions, four proofs), finite/physical/strict audit guards unchanged. Native serialize/read_record/exists/path/lock/nullifier/root/type/owner/Clone and actual durable file/directory effects remain explicit interfaces; ghost Store-at-write argument is erased from native durable_write call and does not establish concurrent native trace. No absent-intent/rollback/no-physical-progress claim on error, and no native/control/full Transfer certification credit.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Persist-intent filesystem fields denote actual independently observed exists/read_record/history results, not authoritative trusted commitments. The write callback carries observed filesystem progress and returned success separately; successful result is not independently proved fsync/file/directory durability. Its Store argument is a ghost of ready=false memory state at invocation, erased in the native signature; native lock/concurrency/memory/physical root and filesystem correspondences remain explicit. Existing intent equality does not infer reader health beyond checked initial readiness/health. Failure retains observed progress and cannot imply intent absence or rollback.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_WRITER_COMMIT_ORDER_INTERRUPTION_AND_POST_READY_CAPACITY_ERROR','SOURCE_PERSIST_INTENT_OBSERVED_PROGRESS_READINESS_AND_IDEMPOTENCE')
s=s.replace('WRITER_COMMIT_SOURCE_COMPLETE_FORTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','PERSIST_INTENT_SOURCE_COMPLETE_FIFTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 9, 'inherited_audits': 486", "'fresh_audits': 10, 'inherited_audits': 495")
s=s.replace('complete forty-nine-module owned root','complete fifty-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source persist-intent observed record/idempotent/write-failure/readiness proof; filesystem progress retained explicitly and native durability not inferred. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':10,'inherited_audits':495,'owned_modules':50})
