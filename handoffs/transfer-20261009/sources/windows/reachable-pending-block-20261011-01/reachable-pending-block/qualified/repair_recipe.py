"""Give ensure-sealed simplification an explicitly instantiated decoded flag equality."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-reachable-pending-block-20261011-02'
s=(old/'generate.py').read_text()
anchor='    simp only [ensureSealed, apply_empty, stored, roundtrip _ frozenCoherent, freeze, if_true]'
new='''    have encodedSealed : (decode (encode (freeze (parentPending decode project final.1)))).sealed = true :=
      congrArg Pending.sealed (roundtrip (freeze (parentPending decode project final.1)) frozenCoherent)
    simp only [ensureSealed, apply_empty, stored, encodedSealed, if_true]'''
assert s.count(anchor)==1; s=s.replace(anchor,new)
assert not (ROOT/'generate.py').exists(); (ROOT/'generate.py').write_text(s)
recipe=(old/'prepare_recipe.py').read_text().replace('transfer-reachable-pending-block-owned-floor-20261011-02','transfer-reachable-pending-block-owned-floor-20261011-03').replace('transfer-reachable-pending-block-regeneration-20261011-02','transfer-reachable-pending-block-regeneration-20261011-03')
anchor="(ROOT/'prepare.py').write_text(s)"; assert recipe.count(anchor)==1
insert="""anchor = \"plan['pins'] += mapping['runtime_sources']\"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+\"failed_reachable_second = DIAG / 'transfer-reachable-pending-block-20261011-02'\\nplan['pins'] += [pin(failed_reachable_second / n) for n in ['repair_recipe.py', 'generate.py', 'regeneration.json', 'prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'generated/TransferReachablePendingBlock01.lean', 'project/ShielddSecurity/TransferReachablePendingBlock01.lean', 'runs/01-TransferReachablePendingBlock01/stdout.txt']]\\n\"+s[pos:]
"""
recipe=recipe.replace(anchor,insert+anchor); (ROOT/'prepare_recipe.py').write_text(recipe)
print({'generator_repair':True,'generated_hand_edits':0,'contract_changes':0,'rejected_attempts':2,'rejected_proof_credit':0})
