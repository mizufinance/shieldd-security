"""Retain failed 01 and unrun 02; finish proof-only observed-error reduction."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-captured-recovery-20261011-02'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferCapturedRecovery01.lean').read_text()
a='''    captured_prepare_equals_original_only_under_forward_partition_contract io store.actualRoots committed intent frames]
'''
b=a+'''  cases observed : (TransferBankRecovery.prepare io store.actualRoots committed intent).error <;> simp only [observed]
'''
assert source.count(a)==1
source=source.replace(a,b)
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferCapturedRecovery01.lean').write_text(source)
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-captured-recovery-owned-floor-20261011-02'"
assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-captured-recovery-owned-floor-20261011-03'")
anchor="plan['pins'] += mapping['runtime_sources']"
assert s.count(anchor)==1
s=s.replace(anchor,"unrun_captured = DIAG / 'transfer-captured-recovery-20261011-02'\nassert not (unrun_captured/'events.jsonl').exists()\nplan['pins'] += [pin(unrun_captured / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'handwritten/TransferCapturedRecovery01.lean', 'project/ShielddSecurity/TransferCapturedRecovery01.lean']]\n"+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Whole strict failed 01 zero credit; prepared 02 never executed and withdrawn before launch after reviewing remaining error. Proof-only explicit observed-error reduction in captured induction and final recovery equality. Program definitions/theorem contracts and explicit native frame premise unchanged. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'proof_only_repair':True,'rejected_whole_attempt_credit':0,'withdrawn02':'UNRUN'})
