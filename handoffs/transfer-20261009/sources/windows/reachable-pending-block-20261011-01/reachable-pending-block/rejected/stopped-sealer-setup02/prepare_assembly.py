"""Seal reachable codec generator successor and full rejected original receipts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-reachable-pending-block-endpoint-20261011-01'
assert not (ROOT/'assemble.py').exists()
recipe=(old/'prepare_assembly.py').read_text(); anchor="(ROOT/'assemble.py').write_text(s)"
assert recipe.count(anchor)==1; recipe=recipe.replace(anchor,'')
scope={'__file__':str(ROOT/'prepare_assembly.py')}; exec(compile(recipe,str(old/'prepare_assembly.py'),'exec'),scope)
s=scope['s'].replace("CURRENT = DIAG / 'transfer-reachable-pending-block-20261011-01'", "CURRENT = DIAG / 'transfer-reachable-pending-block-20261011-02'")
s=s.replace('transfer-reachable-pending-block-checkpoint-20261011-01','transfer-reachable-pending-block-checkpoint-20261011-02')
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"; assert s.count(anchor)==1
extra="""add(CURRENT / 'repair_recipe.py', 'qualified/repair_recipe.py', 'generator proof repair only; no generated hand edit or contract change')
failed = DIAG / 'transfer-reachable-pending-block-20261011-01'
for name in ['generate.py', 'regeneration.json', 'prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'generated/TransferReachablePendingBlock01.lean', 'project/ShielddSecurity/TransferReachablePendingBlock01.lean', 'runs/01-TransferReachablePendingBlock01/stdout.txt']:
    add(failed / name, 'rejected/attempt01/' + name, 'full failed original attempt; zero proof/native/control credit')
old_regeneration = json.loads((failed / 'regeneration.json').read_bytes())
add(old_regeneration['independent_regeneration']['path'], 'rejected/attempt01/regeneration/TransferReachablePendingBlock01.lean', 'retained exact rejected generation; zero credit')
stopped = DIAG / 'transfer-reachable-pending-block-endpoint-20261011-01'
for name in ['prepare_assembly.py', 'assemble.py']:
    add(stopped / name, 'rejected/stopped-sealer-setup01/' + name, 'unexecuted sealer setup; zero credit')
"""
s=s.replace(anchor,extra+anchor).replace("'rejected_attempts': 0", "'rejected_attempts': 1")
(ROOT/'assemble.py').write_text(s)
print({'fresh_successor':True,'rejected_attempts':1,'rejected_proof_credit':0})
