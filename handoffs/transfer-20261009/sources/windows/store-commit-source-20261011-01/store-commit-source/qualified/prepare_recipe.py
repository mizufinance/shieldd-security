"""Prepare symbolic source ordered session commits and retained physical progress."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-persist-intent-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-writer-commit-source-20261011-01'", "UPSTREAM = DIAG / 'transfer-persist-intent-source-20261011-02'")
replace("POOL = DIAG / 'transfer-persist-intent-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-store-commit-source-owned-floor-20261011-02'")
replace("MODULE = 'TransferPersistIntentSource01'", "MODULE = 'TransferStoreCommitSource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferWriterCommitSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferPersistIntentSource01/stdout.txt'")
replace("records.append(('TransferWriterCommitSource01'", "records.append(('TransferPersistIntentSource01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferWriterCommitSource01.lean', 'project/ShielddSecurity/TransferWriterCommitSource01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'repair_recipe.py', 'handwritten/TransferPersistIntentSource01.lean', 'project/ShielddSecurity/TransferPersistIntentSource01.lean']]")
replace('assert len(current) == 9','assert len(current) == 10')
replace('assert len(records) == 50 and len(audits) == 495','assert len(records) == 51 and len(audits) == 505')
replace("'objects': 50", "'objects': 51")
s=s.replace('Complete fifty-module first owned root; 495 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete fifty-one-module first owned root; 505 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 10','assert len(names) == 13')
replace("'imports': ['ShielddSecurity.TransferWriterCommitSource01']", "'imports': ['ShielddSecurity.TransferPersistIntentSource01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Source Store::commit checks ready/health/previous roots/boundary, actual read_record and fallible serialized intent equality before an ordered symbolic list of session commits. Each callback keeps independently observed physical roots on either success or failure; the recurrence stops on a failed participant and preserves its observed roots. Whole returned transition success derives every prior guard/read/serialize/equality, every ordered returned session success at its observed preceding roots, actual observed final roots equality and original returned Prepared transition. Readiness is false after entering participant work even on success, until later Store::complete; original status proof derives unavailability for any observed roots. Unavailable intent refuses before sessions and keeps original Store. Thirteen reports (seven data/program definitions, six proofs), finite/physical/strict audit guards unchanged. Actual native Prepared.sessions order/indices/partition ownership/NOMT root observation/read_record/serialization/lock/type/Clone/durability/async correspondence remains explicit. No native/control/full Transfer certification and no error-implies-rollback or absent-progress claim.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Source commit list denotes Prepared.sessions iteration order and partition indices, not accepted nullifier input list. Callback roots and returned success are independent observations; no root or rollback success premise is inserted. Native actual_roots and session.commit effects/order/ownership, hash/serialization/record equality, prepared validity and lock/concurrency/durable memory correspondence remain explicit. Readiness stays blocked through participant success and final root check; recovery/completion is separate.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_PERSIST_INTENT_OBSERVED_PROGRESS_READINESS_AND_IDEMPOTENCE','SOURCE_STORE_COMMIT_ORDERED_PARTICIPANTS_OBSERVED_ROOTS_AND_BLOCKED_READINESS')
s=s.replace('PERSIST_INTENT_SOURCE_COMPLETE_FIFTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','STORE_COMMIT_SOURCE_COMPLETE_FIFTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 10, 'inherited_audits': 495", "'fresh_audits': 13, 'inherited_audits': 505")
s=s.replace('complete fifty-module owned root','complete fifty-one-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source commit ordered symbolic recurrence and observed root progress/readiness proof; no ancestor replay or native durability inferred. Guards unchanged.'"+s[end:]
anchor = "plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+"failed_writer = DIAG / 'transfer-store-commit-source-20261011-01'\nplan['pins'] += [pin(failed_writer / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferStoreCommitSource01.lean', 'project/ShielddSecurity/TransferStoreCommitSource01.lean', 'runs/01-TransferStoreCommitSource01/stdout.txt']]\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\n"+s[pos:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':13,'inherited_audits':505,'owned_modules':51})
