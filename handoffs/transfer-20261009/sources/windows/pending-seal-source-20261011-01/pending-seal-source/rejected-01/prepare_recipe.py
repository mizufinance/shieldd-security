"""Prepare source SCT one-shot pending seal and whole staging refusal."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-block-pending-sequence-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-pending-set-invariant-20261011-02'", "UPSTREAM = DIAG / 'transfer-block-pending-sequence-20261011-01'")
replace("POOL = DIAG / 'transfer-block-pending-sequence-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-pending-seal-source-owned-floor-20261011-01'")
replace("MODULE = 'TransferBlockPendingSequence01'", "MODULE = 'TransferPendingSealSource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferPendingSetInvariant01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferBlockPendingSequence01/stdout.txt'")
replace("records.append(('TransferPendingSetInvariant01'", "records.append(('TransferBlockPendingSequence01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferPendingSetInvariant01.lean', 'project/ShielddSecurity/TransferPendingSetInvariant01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferBlockPendingSequence01.lean', 'project/ShielddSecurity/TransferBlockPendingSequence01.lean']]")
replace('assert len(current) == 7','assert len(current) == 10')
replace('assert len(records) == 41 and len(audits) == 402','assert len(records) == 42 and len(audits) == 412')
replace("'objects': 41", "'objects': 42")
s=s.replace('Complete forty-one-module first owned root; 402 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete forty-two-module first owned root; 412 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 10','assert len(names) == 13')
replace("'imports': ['ShielddSecurity.TransferPendingSetInvariant01']", "'imports': ['ShielddSecurity.TransferBlockPendingSequence01']")
start=s.index('\nmapping = ')+1; end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'] + ['Pending Sealed membership is derived from the frozen ordered vector, matching enum contains/ordered/Clone branches. Typed enum/getter/put/encoding and actual event/cache/ownership correspondence remain explicit. ensure-sealed accepts object absence, unlike default Open returned by the seal getter.'],
    'scope': 'Source-order SCT one-shot seal/current pending ordered read/ensure-sealed model: object absence defaults to empty Open for seal but ensure-sealed accepts absence; explicit Open refuses ensure, Sealed accepts it. Open seal derives one object write, exact frozen order/coherent membership, preserved V/NV/events cache domains/other object writes, successful ensure, and repeated seal error retaining the actual input cache. Actual current sealed state excludes subsequent full whole delivery request success in either context/every index mode, deriving enclosing exact parent/queue preservation without desired body or callback failure. No NOMT/persistent storage operation, native one-shot control, Host finalization/durability or full Transfer certification is claimed; typed/native/codec/getter/Clone/enum/ownership interfaces remain explicit and wrong-type panics outside returned results. Finite symbolic proofs; zero new native/control credit.'}
""".rstrip()+s[end:]
s=s.replace('WHOLE_TRANSFER_BLOCK_SEQUENCE_DERIVES_GLOBAL_DISTINCT_BOUNDED_PENDING_MEMBERSHIP','SOURCE_PENDING_ONE_SHOT_SEAL_FROZEN_ORDER_ENSURE_BRANCHES_AND_WHOLE_STAGE_REFUSAL')
s=s.replace('BLOCK_PENDING_SEQUENCE_COMPLETE_FORTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','PENDING_SEAL_SOURCE_COMPLETE_FORTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 10, 'inherited_audits': 402", "'fresh_audits': 13, 'inherited_audits': 412")
s=s.replace('complete forty-one-module owned root','complete forty-two-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh exact source-order pending enum one-shot freeze/ensure/current-object framing and full whole-request refusal from current sealed state; qualified ancestors and finite physical/audit guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':13,'inherited_audits':412,'owned_modules':42})
