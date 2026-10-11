"""Seal third generator successor; both rejected proofs and stopped sealers remain zero-credit."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-reachable-pending-block-endpoint-20261011-02/assemble.py').read_text()
anchor="CURRENT = DIAG / 'transfer-reachable-pending-block-20261011-02'"; assert s.count(anchor)==1
s=s.replace(anchor,"CURRENT = DIAG / 'transfer-reachable-pending-block-20261011-03'")
s=s.replace('transfer-reachable-pending-block-checkpoint-20261011-02','transfer-reachable-pending-block-checkpoint-20261011-03')
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"; assert s.count(anchor)==1
extra="""failed_second = DIAG / 'transfer-reachable-pending-block-20261011-02'
for name in ['repair_recipe.py', 'generate.py', 'regeneration.json', 'prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'generated/TransferReachablePendingBlock01.lean', 'project/ShielddSecurity/TransferReachablePendingBlock01.lean', 'runs/01-TransferReachablePendingBlock01/stdout.txt']:
    add(failed_second / name, 'rejected/attempt02/' + name, 'full failed second attempt; zero proof/native/control credit')
second_regeneration = json.loads((failed_second / 'regeneration.json').read_bytes())
add(second_regeneration['independent_regeneration']['path'], 'rejected/attempt02/regeneration/TransferReachablePendingBlock01.lean', 'retained exact rejected second generation; zero credit')
stopped_second = DIAG / 'transfer-reachable-pending-block-endpoint-20261011-02'
for name in ['prepare_assembly.py', 'assemble.py']:
    add(stopped_second / name, 'rejected/stopped-sealer-setup02/' + name, 'unexecuted second sealer setup; zero credit')
"""
s=s.replace(anchor,extra+anchor).replace("'rejected_attempts': 1", "'rejected_attempts': 2")
(ROOT/'assemble.py').write_text(s)
print({'fresh_successor':True,'rejected_attempts':2,'rejected_proof_credit':0})
