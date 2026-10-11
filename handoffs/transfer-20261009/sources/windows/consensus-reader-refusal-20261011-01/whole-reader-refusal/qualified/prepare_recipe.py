"""Prepare five observable whole-body reader refusals at source capacity."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-current-pending-replay-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-nullifier-object-keys-20261011-01'", "UPSTREAM = DIAG / 'transfer-nullifier-consensus-limits-20261011-02'")
s=s.replace('transfer-current-pending-replay-owned-floor-20261011-01','transfer-whole-reader-refusal-owned-floor-20261011-01')
replace("MODULE = 'TransferCurrentPendingReplay01'", "MODULE = 'TransferWholeReaderRefusal01'")
replace("stdout = UPSTREAM / 'runs/01-TransferNullifierObjectKeys01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferNullifierConsensusLimits01/stdout.txt'")
replace("records.append(('TransferNullifierObjectKeys01'", "records.append(('TransferNullifierConsensusLimits01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'generated/TransferNullifierObjectKeys01.lean', 'project/ShielddSecurity/TransferNullifierObjectKeys01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'generated/TransferNullifierConsensusLimits01.lean', 'project/ShielddSecurity/TransferNullifierConsensusLimits01.lean']]")
replace('assert len(records) == 35 and len(audits) == 343','assert len(records) == 39 and len(audits) == 386')
replace("'objects': 35", "'objects': 39")
s=s.replace('Complete thirty-five-module first owned root; 343 inherited full reports.', 'Complete thirty-nine-module first owned root; 386 inherited full reports including seventeen Readback reports exactly once.')
replace('assert len(names) == 8','assert len(names) == 9')
replace("'imports': ['ShielddSecurity.TransferNullifierObjectKeys01']", "'imports': ['ShielddSecurity.TransferNullifierConsensusLimits01']")
start=s.index("runtime_rows = "); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Config bundles existing explicit model arguments; delivery instantiates the same complete body/current typed Reader/boundary/lock/verified status/index program at exact source consensus capacity, not an arbitrary body callback. Whole success for an actual member derives all reader observations. Actual original-parent Reader object absence, failed authenticated boundary observation, unavailable read-lock observation, stale typed Store boundary, or an authenticated spent leaf under the explicit MerkleContract excludes whole success and derives enclosing finish preservation of the exact original parent/deferred queue. Both proof contexts/every index mode/arbitrary registry/exclusivity, extractor/note/volume/index/proof outcomes covered. No caller-supplied body failure, desired index error or successful primitive premise. Input membership and selected supported 32/64-bit word width explicit; missing-boundary/lock and stale-store observations remain modeled operational facts. Wrong-type/loader panics outside returned results; boundary/native/NOMT/hash/proof/typed/codec/crypto/ownership/Host/durability and full Transfer certification remain open. These are formal refusal proofs, not executed semantic negative controls; zero new native/control credit.'}
""".rstrip()+s[end:]
s=s.replace('CURRENT_PENDING_OBJECT_READ_DERIVES_TWO_ACTION_SHARED_INPUT_REPLAY_REFUSAL','WHOLE_TRANSFER_OBSERVABLE_READER_FAILURE_OR_AUTHENTICATED_SPENT_REFUSES_AND_PRESERVES_PARENT_QUEUE')
s=s.replace('CURRENT_PENDING_REPLAY_COMPLETE_THIRTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WHOLE_READER_REFUSAL_COMPLETE_THIRTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 8, 'inherited_audits': 343", "'fresh_audits': 9, 'inherited_audits': 386")
s=s.replace('complete thirty-five-module owned root','complete thirty-nine-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh small reusable whole-success observations and finish refusal lemma; five observable whole reader refusal/preservation theorems at source consensus capacity; finite symbolic proofs; qualified ancestors and guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':9,'inherited_audits':386,'owned_modules':39})
