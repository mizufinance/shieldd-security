"""Close impossible Option cases and use already rewritten case receipts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-store-commit-source-20261011-01'
s=(old/'handwritten/TransferStoreCommitSource01.lean').read_text()
changes=[
('| none => simp only [read] at success','| none =>\n      simp only [read] at success\n      cases success'),
('| none => simp only [read, serialized] at success','| none =>\n        simp only [read, serialized] at success\n        cases success'),
('⟨gate, record, bytes, read, serialized, equal, checked.1,','⟨gate, record, bytes, rfl, rfl, equal, checked.1,'),
('· simp only [read, serialized, if_neg equal] at success','· simp only [read, serialized, if_neg equal] at success\n          cases success')]
for a,b in changes:
    assert s.count(a)==1,a
    s=s.replace(a,b)
p=ROOT/'handwritten/TransferStoreCommitSource01.lean'; assert not p.exists(); p.parent.mkdir(); p.write_text(s)
recipe=(old/'prepare_recipe.py').read_text().replace('transfer-store-commit-source-owned-floor-20261011-01','transfer-store-commit-source-owned-floor-20261011-02')
anchor="(ROOT/'prepare.py').write_text(s)"; assert recipe.count(anchor)==1
insert="""anchor = "plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+"failed_writer = DIAG / 'transfer-store-commit-source-20261011-01'\\nplan['pins'] += [pin(failed_writer / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferStoreCommitSource01.lean', 'project/ShielddSecurity/TransferStoreCommitSource01.lean', 'runs/01-TransferStoreCommitSource01/stdout.txt']]\\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\\n"+s[pos:]
"""
recipe=recipe.replace(anchor,insert+anchor); (ROOT/'prepare_recipe.py').write_text(recipe)
print({'program_changes':0,'contract_changes':0,'rejected_proof_credit':0})
