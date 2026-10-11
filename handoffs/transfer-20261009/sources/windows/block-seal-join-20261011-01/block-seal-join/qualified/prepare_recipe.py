"""Prepare full block/seal join with source-compatible encoded default start."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-pending-seal-source-20261011-03/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-block-pending-sequence-20261011-01'", "UPSTREAM = DIAG / 'transfer-pending-seal-source-20261011-03'")
replace("POOL = DIAG / 'transfer-pending-seal-source-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-block-seal-join-owned-floor-20261011-01'")
replace("MODULE = 'TransferPendingSealSource01'", "MODULE = 'TransferBlockSealJoin01'")
replace("stdout = UPSTREAM / 'runs/01-TransferBlockPendingSequence01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferPendingSealSource01/stdout.txt'")
replace("records.append(('TransferBlockPendingSequence01'", "records.append(('TransferPendingSealSource01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferBlockPendingSequence01.lean', 'project/ShielddSecurity/TransferBlockPendingSequence01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferPendingSealSource01.lean', 'project/ShielddSecurity/TransferPendingSealSource01.lean']]")
replace('assert len(current) == 10','assert len(current) == 13')
replace('assert len(records) == 42 and len(audits) == 412','assert len(records) == 43 and len(audits) == 425')
replace("'objects': 42", "'objects': 43")
s=s.replace('Complete forty-two-module first owned root; 412 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete forty-three-module first owned root; 425 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 13','assert len(names) == 5')
replace("'imports': ['ShielddSecurity.TransferBlockPendingSequence01']", "'imports': ['ShielddSecurity.TransferPendingSealSource01']")
start=s.index('\nmapping = ')+1; end=s.index("\nmapping_file =",start)
s=s[:start]+"""runtime_rows = {row['path']: row for row in prior_mapping['runtime_sources']}
for relative in ['crates/core/component/sct/src/component/sct.rs', 'crates/core/app/src/app/host.rs']:
    row = pin(runtime / relative)
    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
    runtime_rows[row['path']] = row
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),
    'interfaces': prior_mapping['interfaces'] + ['Pinned SCT begin_block writes explicit PendingNullifierBlock::default Open empty; encoded default under typed representation derives the empty starting read. The modeled complete block walk/one-shot seal must match actual native phase/request scheduling, Arc uniqueness, intervening state mutation and writer accepted-vector Clone/collect before native Host/durability correspondence is claimed. SCT end_block expect panics remain outside returned error results.'],
    'scope': 'Same arbitrary successful whole-delivery block walk joined to source one-shot sealing. Encoded default Open empty derives an empty initial current getter, matching the actual SCT begin_block initialization instead of requiring object absence. Empty initial read derives global order/distinctness/bounded membership; nonempty successful walks retain an actual encoded Open object and refuse ensure-sealed before sealing. Source seal then succeeds, preserves state V/NV and empty seal events, freezes exact concatenated global input order/membership with Nodup/32768 bound, passes ensure, rejects repeated seal retaining empty retry cache, and refuses every later whole delivery request with sealed parent/deferred queue preserved. All intermediate invariants and failure outcomes derived; initial default representation, typed encode/decode roundtrip, injective key representation, request nonempty/supported widths explicit. Native phase/scheduling/Arc/getter/Clone/owner accepted-vector/codec/proof/Host/durability and full Transfer remain open; no NOMT operation or native/semantic-control credit. Finite symbolic list induction.'}
""".rstrip()+s[end:]
s=s.replace('SOURCE_PENDING_ONE_SHOT_SEAL_FROZEN_ORDER_ENSURE_BRANCHES_AND_WHOLE_STAGE_REFUSAL','SOURCE_DEFAULT_OPEN_BLOCK_WALK_AND_ONE_SHOT_SEAL_DERIVE_FROZEN_GLOBAL_INPUTS')
s=s.replace('PENDING_SEAL_SOURCE_COMPLETE_FORTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','BLOCK_SEAL_JOIN_COMPLETE_FORTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 13, 'inherited_audits': 412", "'fresh_audits': 5, 'inherited_audits': 425")
s=s.replace('complete forty-two-module owned root','complete forty-three-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh same-program whole-block/one-shot seal join, typed actual encoded default initialization and exact frozen global inputs; all intermediate state invariants derived; source/finite/physical/audit guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':5,'inherited_audits':425,'owned_modules':43})
