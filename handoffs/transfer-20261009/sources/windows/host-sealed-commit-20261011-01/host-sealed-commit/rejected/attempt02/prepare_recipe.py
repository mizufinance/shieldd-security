"""Retain strict failed Host source; repair record layout and reflexive proof reduction."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-host-sealed-commit-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferHostSealedCommit01.lean').read_text()
a='''      ⟨{host with phase := .idle, writer := result.phase, active := reset io result.store,
        blockId := none, store := result.store}, committed.applicationRoot⟩'''
b='''      ⟨{host with phase := .idle, writer := result.phase, active := reset io result.store, blockId := none, store := result.store}, committed.applicationRoot⟩'''
assert source.count(a)==1
source=source.replace(a,b)
a='''  simp only [commitSealed, sealedHost, failed]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩'''
b='''  simp [commitSealed, sealedHost, failed]'''
assert source.count(a)==1
source=source.replace(a,b)
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferHostSealedCommit01.lean').write_text(source)
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-host-sealed-commit-owned-floor-20261011-01'"
assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-host-sealed-commit-owned-floor-20261011-02'")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
s=s.replace(anchor,"rejected_host = DIAG / 'transfer-host-sealed-commit-20261011-01'\nplan['pins'] += [pin(rejected_host / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferHostSealedCommit01.lean', 'project/ShielddSecurity/TransferHostSealedCommit01.lean', 'runs/01-TransferHostSealedCommit01/stdout.txt']]\n"+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Whole strict failed 01 zero credit, including compiler-generated placeholders after record-layout parse error; source contains no sorry/admit/axioms. Idle record update field layout normalized to one line with no intended program change. Failure proof uses ordinary simplification of reflexive conjunction instead of rfl against simplified True. Theorem contracts and source scope unchanged. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'layout_and_proof_only_repair':True,'rejected_proof_credit':0})
