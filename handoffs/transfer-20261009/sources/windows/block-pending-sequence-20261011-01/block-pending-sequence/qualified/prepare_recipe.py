"""Prepare finite whole-delivery block sequence on complete qualified closure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-pending-set-invariant-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-whole-reader-refusal-20261011-01'", "UPSTREAM = DIAG / 'transfer-pending-set-invariant-20261011-02'")
s=s.replace("POOL = DIAG / 'transfer-pending-set-invariant-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-block-pending-sequence-owned-floor-20261011-01'")
replace("MODULE = 'TransferPendingSetInvariant01'", "MODULE = 'TransferBlockPendingSequence01'")
replace("stdout = UPSTREAM / 'runs/01-TransferWholeReaderRefusal01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferPendingSetInvariant01/stdout.txt'")
replace("records.append(('TransferWholeReaderRefusal01'", "records.append(('TransferPendingSetInvariant01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferWholeReaderRefusal01.lean', 'project/ShielddSecurity/TransferWholeReaderRefusal01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferPendingSetInvariant01.lean', 'project/ShielddSecurity/TransferPendingSetInvariant01.lean']]")
replace('assert len(current) == 9','assert len(current) == 7')
replace('assert len(records) == 40 and len(audits) == 395','assert len(records) == 41 and len(audits) == 402')
replace("'objects': 40", "'objects': 41")
s=s.replace('Complete forty-module first owned root; 395 inherited full reports including seventeen Readback reports exactly once.', 'Complete forty-one-module first owned root; 402 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 7','assert len(names) == 10')
replace("'imports': ['ShielddSecurity.TransferWholeReaderRefusal01']", "'imports': ['ShielddSecurity.TransferPendingSetInvariant01']")
start=s.index('\nmapping = ')+1; end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'] + ['Sequence requests explicitly have nonempty input projections and supported 32/64-bit word widths. Every step installs the same typed pending encoding/roundtrip/current getter and injective static key representation. All successful whole run outcomes are supplied as one walk success, not successful primitive or desired poststate contracts. Matching actual native request projection/scheduling and imbl collections remains an interface.'],
    'scope': 'Compose arbitrary finite lists of complete-Item whole delivery model calls with mixed proof contexts/index modes/registries/exclusivity/configurations. Each step installs fixed typed pending encoding/current object getter at exact source-derived static keys and source consensus capacity; every per-step pending invariant/order/encoding derives from actual whole success. The successful symbolic walk derives final pending order equal to initial order plus concatenated actual input projections, coherent membership, no duplicate ordered nullifiers and consensus capacity bound. Actual initial pending-object absence derives empty invariant, so the entire concatenated block input sequence is duplicate-free, bounded by 32768, and exactly represented by final pending membership. No desired next invariant or successful primitive callback supplied. Nonempty projections, supported word widths, typed encode/decode roundtrip and injective key representation explicit. Walk projects state/deferred queue only; event publication, block rollback, sealing, Host finalization/durability and actual native request scheduling not certified. Other native/typed/getter/codec/store/crypto/ownership interfaces and full Transfer certification remain open. Finite list induction; zero native/semantic control credit.'}
""".rstrip()+s[end:]
s=s.replace('SYMBOLIC_PENDING_SET_ORDERED_VECTOR_COHERENCE_AND_DUPLICATE_FREE_APPEND','WHOLE_TRANSFER_BLOCK_SEQUENCE_DERIVES_GLOBAL_DISTINCT_BOUNDED_PENDING_MEMBERSHIP')
s=s.replace('PENDING_SET_INVARIANT_COMPLETE_FORTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','BLOCK_PENDING_SEQUENCE_COMPLETE_FORTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 7, 'inherited_audits': 395", "'fresh_audits': 10, 'inherited_audits': 402")
s=s.replace('complete forty-module owned root','complete forty-one-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite actual-whole-delivery sequence with typed current pending binding, source-derived keys/consensus capacity and global list induction; no unrolled wide walk; qualified ancestors and all guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':10,'inherited_audits':402,'owned_modules':41})
