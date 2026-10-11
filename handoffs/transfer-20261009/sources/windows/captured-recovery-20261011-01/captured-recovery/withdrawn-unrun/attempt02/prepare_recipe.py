"""Proof-only reduction repair; retain entire failed captured recurrence attempt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-captured-recovery-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferCapturedRecovery01.lean').read_text()
a='''      | some error => rfl
      | none =>
        apply ih'''
b='''      | some error => simp only [observed]
      | none =>
        simp only [observed]
        apply ih'''
assert source.count(a)==1
source=source.replace(a,b)
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferCapturedRecovery01.lean').write_text(source)
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-captured-recovery-owned-floor-20261011-01'"
assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-captured-recovery-owned-floor-20261011-02'")
anchor="plan['pins'] += mapping['runtime_sources']"
assert s.count(anchor)==1
s=s.replace(anchor,"rejected_captured = DIAG / 'transfer-captured-recovery-20261011-01'\nplan['pins'] += [pin(rejected_captured / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferCapturedRecovery01.lean', 'project/ShielddSecurity/TransferCapturedRecovery01.lean', 'runs/01-TransferCapturedRecovery01/stdout.txt']]\n"+anchor)
a="plan['source_repairs'] = 'Fresh symbolic source captured-initial recurrence and explicitly conditional original recovery bridge. Native frame contract remains a premise. No original recovery replay or native/control/certification credit. Guards unchanged.'"
assert s.count(a)==1
s=s.replace(a,"plan['source_repairs'] = 'Whole strict failed 01 retained with zero credit. Only captured rollback induction proof reduces actual observed callback error under let before closing the match branches. Program definitions and theorem contracts, explicit native partition frame premise and all guards unchanged. No ancestor replay or native/control/certification credit.'")
(ROOT/'prepare.py').write_text(s)
print({'proof_only_repair':True,'rejected_whole_attempt_credit':0})
