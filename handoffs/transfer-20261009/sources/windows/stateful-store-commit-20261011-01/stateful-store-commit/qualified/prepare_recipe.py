"""Retain rejected strict attempt, repair only the session-frame induction proof."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-stateful-store-commit-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferStatefulStoreCommit01.lean').read_text()
a='''    unfold walkSessions
    split
    next succeeded => exact ih _
    next failed => exact ⟨rfl, rfl⟩'''
b='''    by_cases succeeded : (commit index store).succeeded = true
    · simp only [walkSessions, if_pos succeeded]
      exact ih _
    · simp only [walkSessions, if_neg succeeded]
      exact ⟨rfl, rfl⟩'''
assert source.count(a)==1
source=source.replace(a,b)
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferStatefulStoreCommit01.lean').write_text(source)
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-stateful-store-commit-owned-floor-20261011-01'"
assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-stateful-store-commit-owned-floor-20261011-02'")
anchor="plan['pins'] += mapping['runtime_sources']"
assert s.count(anchor)==1
s=s.replace(anchor,"rejected_stateful = DIAG / 'transfer-stateful-store-commit-20261011-01'\nplan['pins'] += [pin(rejected_stateful / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferStatefulStoreCommit01.lean', 'project/ShielddSecurity/TransferStatefulStoreCommit01.lean', 'runs/01-TransferStatefulStoreCommit01/stdout.txt']]\n"+anchor)
a="plan['source_repairs'] = 'Fresh handwritten temporal state threading with independent actual physical/health observations; no ancestor replay, native control or physical durability credit. Guards unchanged.'"
assert s.count(a)==1
s=s.replace(a,"plan['source_repairs'] = 'Retained whole strict failed 01 has zero proof credit. Only session-owned-frame lemma induction proof changes from split on repeated let projections to explicit by_cases plus reduction. All program definitions, theorem contracts, independently observed roots/health and source scope unchanged. Guards unchanged.'")
(ROOT/'prepare.py').write_text(s)
print({'proof_only_repair':True,'rejected_whole_attempt_credit':0})
