"""Fix try tactic grouping only; preserve both strict failed attempts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-host-sealed-commit-20261011-02'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferHostSealedCommit01.lean').read_text()
a='cases phase : host.phase <;> try exact False.elim (unsealed phase) <;> simp only [commitSealed, phase]'
b='cases phase : host.phase <;> try (exact False.elim (unsealed phase)) <;> simp only [commitSealed, phase]'
assert source.count(a)==1
source=source.replace(a,b)
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferHostSealedCommit01.lean').write_text(source)
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-host-sealed-commit-owned-floor-20261011-02'"
assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-host-sealed-commit-owned-floor-20261011-03'")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
s=s.replace(anchor,"rejected_host02 = DIAG / 'transfer-host-sealed-commit-20261011-02'\nplan['pins'] += [pin(rejected_host02 / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferHostSealedCommit01.lean', 'project/ShielddSecurity/TransferHostSealedCommit01.lean', 'runs/01-TransferHostSealedCommit01/stdout.txt']]\n"+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Whole strict failed 01/02 retained zero credit. Final other-phase lemma wraps try tactic in parentheses so simplification runs for non-Sealed cases. Earlier grammar layout and reflexive proof repair retained. All intended program definitions/theorem contracts unchanged; source contains no sorry/admit/axioms. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'proof_tactic_grouping_only_repair':True,'rejected_whole_attempts':2,'rejected_proof_credit':0})
