"""Prepare exact generated consensus-capacity wrappers on the complete closure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-current-pending-replay-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-nullifier-object-keys-20261011-01'", "UPSTREAM = DIAG / 'transfer-whole-durable-readback-20261011-02'")
s=s.replace('transfer-current-pending-replay-owned-floor-20261011-01','transfer-nullifier-consensus-limits-owned-floor-20261011-01')
replace("MODULE = 'TransferCurrentPendingReplay01'", "MODULE = 'TransferNullifierConsensusLimits01'")
replace("stdout = UPSTREAM / 'runs/01-TransferNullifierObjectKeys01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferWholeDurableReadback01/stdout.txt'")
replace("records.append(('TransferNullifierObjectKeys01'", "records.append(('TransferWholeDurableReadback01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'generated/TransferNullifierObjectKeys01.lean', 'project/ShielddSecurity/TransferNullifierObjectKeys01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferWholeDurableReadback01.lean', 'project/ShielddSecurity/TransferWholeDurableReadback01.lean']]")
replace('assert len(current) == 7','assert len(current) == 11')
replace('assert len(records) == 35 and len(audits) == 343','assert len(records) == 38 and len(audits) == 379')
replace("'objects': 35", "'objects': 38")
s=s.replace('Complete thirty-five-module first owned root; 343 inherited full reports.', 'Complete thirty-eight-module first owned root; 379 inherited full reports including seventeen original Readback reports exactly once.')
replace('assert len(names) == 8','assert len(names) == 7')
replace("handwritten = ROOT / 'handwritten' / (MODULE + '.lean')", "handwritten = ROOT / 'generated' / (MODULE + '.lean')")
replace("'imports': ['ShielddSecurity.TransferNullifierObjectKeys01']", "'imports': ['ShielddSecurity.TransferWholeDurableReadback01']")
start=s.index("runtime_rows = "); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'] + ['The selected model usize width must be 32 or 64; matching the concrete native target and Rust saturating/len arithmetic remains an explicit representation interface. The source consensus limit is extracted exactly, and its strict bound below either selected maximum is kernel proved.'],
    'scope': 'Generate exact Rust MAX_NULLIFIERS_PER_BLOCK = 32_768, model maximum 2^width-1 for explicitly selected 32/64-bit usize, and prove the capacity inequality. Instantiate qualified whole-delivery verified unspent status, conditional Merkle authenticated absence, and first-success/shared-input replay refusal/first-parent-and-queue preservation with the source consensus capacity. No caller-selected capacity or below-word inequality premise remains in these three whole contracts. Selected native word-width and all typed object/getter/Clone/boundary/NOMT/hash/proof/Merkle/crypto/Host/durability correspondence interfaces remain explicit. Exact pinned source/qualified signatures and independent byte-exact regeneration retained; no generated Lean or evidence hand-edited. Full Transfer certification remains open; no new native/control credit.'}
""".rstrip()+s[end:]
s=s.replace('CURRENT_PENDING_OBJECT_READ_DERIVES_TWO_ACTION_SHARED_INPUT_REPLAY_REFUSAL','EXACT_SOURCE_NULLIFIER_CONSENSUS_CAPACITY_DISCHARGES_WHOLE_DELIVERY_WORD_BOUND')
s=s.replace('CURRENT_PENDING_REPLAY_COMPLETE_THIRTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','NULLIFIER_CONSENSUS_LIMITS_COMPLETE_THIRTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 8, 'inherited_audits': 343", "'fresh_audits': 7, 'inherited_audits': 379")
s=s.replace('complete thirty-five-module owned root','complete thirty-eight-module owned root')
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
s=s.replace(needle,"""generation = json.loads((ROOT / 'generation.json').read_bytes())
assert generation['output'] == pin(handwritten)
assert generation['generator'] == pin(ROOT / 'generate.py')
regeneration = DIAG / 'transfer-nullifier-consensus-limits-regeneration-20261011-01'
assert handwritten.read_bytes() == (regeneration / ('generated/' + MODULE + '.lean')).read_bytes()
plan['pins'] += [pin(ROOT / n) for n in ['generate.py', 'generation.json']]
plan['pins'] += [pin(regeneration / n) for n in ['generation.json', 'generated/' + MODULE + '.lean']]
plan['pins'] += generation['runtime_sources'] + generation['upstream_contract_sources']
rejected_durable = DIAG / 'transfer-whole-durable-readback-20261011-01'
plan['pins'] += [pin(rejected_durable / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferWholeDurableReadback01.lean',
    'project/ShielddSecurity/TransferWholeDurableReadback01.lean', 'runs/01-TransferWholeDurableReadback01/stdout.txt']]
"""+needle)
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Maintained exact-source consensus limit generation with derived width bound and unchanged qualified whole-delivery premises/conclusions; independent exact regeneration; no hand-edited output; guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_audits':379,'owned_modules':38})
