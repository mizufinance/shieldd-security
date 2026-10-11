"""Prepare whole reachable codec block/freeze proof, with independent generation check."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-pending-finite-codec-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-prepared-accepted-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-pending-finite-codec-20261011-02'")
replace("POOL = DIAG / 'transfer-pending-finite-codec-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-reachable-pending-block-owned-floor-20261011-03'")
replace("MODULE = 'TransferPendingFiniteCodec01'", "MODULE = 'TransferReachablePendingBlock01'")
replace("stdout = UPSTREAM / 'runs/01-TransferPreparedAcceptedSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferPendingFiniteCodec01/stdout.txt'")
replace("records.append(('TransferPreparedAcceptedSource01'", "records.append(('TransferPendingFiniteCodec01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferPreparedAcceptedSource01.lean', 'project/ShielddSecurity/TransferPreparedAcceptedSource01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferPendingFiniteCodec01.lean', 'project/ShielddSecurity/TransferPendingFiniteCodec01.lean']]")
replace('assert len(current) == 10','assert len(current) == 12')
replace('assert len(records) == 45 and len(audits) == 440','assert len(records) == 46 and len(audits) == 452')
replace("'objects': 45", "'objects': 46")
s=s.replace('Complete forty-five-module first owned root; 440 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete forty-six-module first owned root; 452 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 12','assert len(names) == 7')
replace("handwritten = ROOT / 'handwritten' / (MODULE + '.lean')", "handwritten = ROOT / 'generated' / (MODULE + '.lean')")
replace("'imports': ['ShielddSecurity.TransferPreparedAcceptedSource01']", "'imports': ['ShielddSecurity.TransferPendingFiniteCodec01']")
replace("plan['pins'].append(pin(ROOT / 'repair_recipe.py'))", "plan['pins'].append(pin(UPSTREAM / 'repair_recipe.py'))")
anchor="source = handwritten.read_text()"; assert s.count(anchor)==1
extra="""
regenerated = DIAG / 'transfer-reachable-pending-block-regeneration-20261011-03/TransferReachablePendingBlock01.lean'
assert regenerated.read_bytes() == handwritten.read_bytes()
regeneration = {'generated': pin(handwritten), 'independent_regeneration': pin(regenerated), 'byte_exact': True,
    'generator': pin(ROOT / 'generate.py'), 'kernel_credit': 0}
dump(ROOT / 'regeneration.json', regeneration)
"""
s=s.replace(anchor,anchor+extra)
anchor="plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
s=s.replace(anchor,"plan['pins'] += [pin(ROOT / 'generate.py'), pin(ROOT / 'regeneration.json'), pin(regenerated)]\n"+anchor)
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Same source whole delivery step/list walk/one-shot seal proved with a coherence-restricted pending codec. Actual successful inspection derives next coherence before decoding the stored encoding; finite walk induction propagates invariant and exact global input order; freeze is coherent by construction. Finite enum wrapper starts from the encoded native-default Open empty, uses only observational typed finite-enum restoration, and derives successful seal, state V/NV/event frames, exact frozen concatenated input order, global Nodup/32768 bound/membership, ensure success, empty-cache repeated-seal refusal and every later whole request refusal with parent/deferred queue preserved. It does not assume any native roundtrip for arbitrary model membership functions or desired intermediate pending invariants. Native Sealed stores ordered only; restored membership is an explicit derived ghost. Seven complete reports (one full facts definition and six proofs), exact independently regenerated source and unchanged finite/physical guards. Native typed object embedding/Clone, finite collections/SDK nullifier representation, reader/proof/crypto/phase/scheduling/owner/Host/durability remain explicit; full Transfer remains open, zero native/control credit.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['This fresh same-program proof consumes roundtrip only for derived coherent reachable pending states. The finite enum wrapper uses observational typed finite encoding/restoration and reconstructs Sealed membership as a ghost; it never instantiates the prior universal arbitrary-Pending codec assumption. Native finite list/set/nullifier representation, cnidarium typed object embedding/Clone and complete program scheduling/ownership remain independent correspondence interfaces.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('FINITE_PENDING_ENUM_ERASURE_GHOST_AND_REACHABLE_COHERENT_CODEC','WHOLE_REACHABLE_PENDING_CODEC_BLOCK_FREEZE_WITH_FINITE_ENUM_GHOST')
s=s.replace('FINITE_PENDING_CODEC_COMPLETE_FORTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','REACHABLE_PENDING_BLOCK_COMPLETE_FORTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 12, 'inherited_audits': 440", "'fresh_audits': 7, 'inherited_audits': 452")
s=s.replace('complete forty-five-module owned root','complete forty-six-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh whole same-program block/freeze proof with coherence-restricted codec and finite enum observational restoration wrapper; exact maintained generator and independent regeneration. Physical/audit guards unchanged.'"+s[end:]
anchor = "plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+"failed_reachable = DIAG / 'transfer-reachable-pending-block-20261011-01'\nplan['pins'] += [pin(failed_reachable / n) for n in ['generate.py', 'regeneration.json', 'prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'generated/TransferReachablePendingBlock01.lean', 'project/ShielddSecurity/TransferReachablePendingBlock01.lean', 'runs/01-TransferReachablePendingBlock01/stdout.txt']]\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\n"+s[pos:]
anchor = "plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+"failed_reachable_second = DIAG / 'transfer-reachable-pending-block-20261011-02'\nplan['pins'] += [pin(failed_reachable_second / n) for n in ['repair_recipe.py', 'generate.py', 'regeneration.json', 'prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'generated/TransferReachablePendingBlock01.lean', 'project/ShielddSecurity/TransferReachablePendingBlock01.lean', 'runs/01-TransferReachablePendingBlock01/stdout.txt']]\n"+s[pos:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_audits':452,'owned_modules':46})
