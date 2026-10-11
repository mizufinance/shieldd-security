"""Repair the generated proof through its generator; preserve all original receipts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-reachable-pending-block-20261011-01'
s=(old/'generate.py').read_text()
anchor="new_ensure='''  · have frozenCoherent"
replacement="new_ensure='''  · change ensureSealed decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨sealedState, (empty : Cache O Unit)⟩ = .ok ()\n    have frozenCoherent"
assert s.count(anchor)==1; s=s.replace(anchor,replacement)
assert not (ROOT/'generate.py').exists(); (ROOT/'generate.py').write_text(s)
recipe=(old/'prepare_recipe.py').read_text().replace('transfer-reachable-pending-block-owned-floor-20261011-01','transfer-reachable-pending-block-owned-floor-20261011-02').replace('transfer-reachable-pending-block-regeneration-20261011-01','transfer-reachable-pending-block-regeneration-20261011-02')
anchor="(ROOT/'prepare.py').write_text(s)"; assert recipe.count(anchor)==1
insert="""anchor = \"plan['pins'] += mapping['runtime_sources']\"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+\"failed_reachable = DIAG / 'transfer-reachable-pending-block-20261011-01'\\nplan['pins'] += [pin(failed_reachable / n) for n in ['generate.py', 'regeneration.json', 'prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'generated/TransferReachablePendingBlock01.lean', 'project/ShielddSecurity/TransferReachablePendingBlock01.lean', 'runs/01-TransferReachablePendingBlock01/stdout.txt']]\\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\\n\"+s[pos:]
"""
recipe=recipe.replace(anchor,insert+anchor); (ROOT/'prepare_recipe.py').write_text(recipe)
print({'generator_repair':True,'generated_hand_edits':0,'contract_changes':0,'rejected_proof_credit':0})
