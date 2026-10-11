"""Prepare reusable symbolic pending membership/ordered uniqueness lemmas."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-whole-reader-refusal-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-nullifier-consensus-limits-20261011-02'", "UPSTREAM = DIAG / 'transfer-whole-reader-refusal-20261011-01'")
s=s.replace('transfer-whole-reader-refusal-owned-floor-20261011-01','transfer-pending-set-invariant-owned-floor-20261011-01')
replace("MODULE = 'TransferWholeReaderRefusal01'", "MODULE = 'TransferPendingSetInvariant01'")
replace("stdout = UPSTREAM / 'runs/01-TransferNullifierConsensusLimits01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferWholeReaderRefusal01/stdout.txt'")
replace("records.append(('TransferNullifierConsensusLimits01'", "records.append(('TransferWholeReaderRefusal01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'generated/TransferNullifierConsensusLimits01.lean', 'project/ShielddSecurity/TransferNullifierConsensusLimits01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferWholeReaderRefusal01.lean', 'project/ShielddSecurity/TransferWholeReaderRefusal01.lean']]")
replace('assert len(current) == 7','assert len(current) == 9')
replace('assert len(records) == 39 and len(audits) == 386','assert len(records) == 40 and len(audits) == 395')
replace("'objects': 39", "'objects': 40")
s=s.replace('Complete thirty-nine-module first owned root; 386 inherited full reports including seventeen Readback reports exactly once.', 'Complete forty-module first owned root; 395 inherited full reports including seventeen Readback reports exactly once.')
replace('assert len(names) == 9','assert len(names) == 7')
replace("'imports': ['ShielddSecurity.TransferNullifierConsensusLimits01']", "'imports': ['ShielddSecurity.TransferWholeReaderRefusal01']")
start=s.index("mapping = "); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'] + ['Initial Open pending membership equals ordered-vector membership, and the initial ordered vector has no duplicates, are explicit data invariants; default empty has both proved. Native imbl Vector/OrdSet/getter/Clone correspondence remains separate. Successful symbolic uniqueLoop and pending freshness derive admitted append uniqueness.'],
    'scope': 'Small symbolic Coherent/Invariant predicates, default-empty invariant, membership coherence preservation, uniqueLoop-derived Nodup/freshness, admitted cross-list append Nodup, and successful actual stage inspection invariant. Source uses reusable finite list induction and qualified source-order primitive success; initial coherence/ordered Nodup and generic capacity-below-word premise explicit for later source-consensus whole-delivery composition. No desired next-state invariant, unrolled constraint walk or primitive callback contract supplied. Typed/native collections/getter/Clone/codec/store/crypto/ownership/Host/durability and full Transfer certification remain open. Zero new native or executed semantic-control credit.'}
""".rstrip()+s[end:]
s=s.replace('WHOLE_TRANSFER_OBSERVABLE_READER_FAILURE_OR_AUTHENTICATED_SPENT_REFUSES_AND_PRESERVES_PARENT_QUEUE','SYMBOLIC_PENDING_SET_ORDERED_VECTOR_COHERENCE_AND_DUPLICATE_FREE_APPEND')
s=s.replace('WHOLE_READER_REFUSAL_COMPLETE_THIRTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','PENDING_SET_INVARIANT_COMPLETE_FORTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 9, 'inherited_audits': 386", "'fresh_audits': 7, 'inherited_audits': 395")
s=s.replace('complete thirty-nine-module owned root','complete forty-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh small reusable symbolic pending set/vector list invariants for live whole/block-delivery claim; source-order uniqueness/freshness derived; qualified ancestors and finite guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_audits':395,'owned_modules':40})
