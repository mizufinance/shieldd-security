"""Fresh explicit gate decider and case-rewritten reflexivity proof repairs."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-prepared-accepted-source-20261011-01'
source=(old/'handwritten/TransferPreparedAcceptedSource01.lean').read_text()
old_body=': Option Prepared :=\n  if Gate backend previous height accepted then'
new_body=': Option Prepared := by\n  letI : Decidable (Gate backend previous height accepted) := by unfold Gate; infer_instance\n  exact if Gate backend previous height accepted then'
assert source.count(old_body)==1
source=source.replace(old_body,new_body)
assert source.count('roots, observed, rfl, rfl, rfl, rfl, rfl')==1
source=source.replace('roots, observed, rfl, rfl, rfl, rfl, rfl','roots, rfl, rfl, rfl, rfl, rfl, rfl')
target=ROOT/'handwritten/TransferPreparedAcceptedSource01.lean'
assert not target.exists(); target.parent.mkdir()
target.write_text(source)
recipe=(old/'prepare_recipe.py').read_text().replace('transfer-prepared-accepted-source-owned-floor-20261011-01','transfer-prepared-accepted-source-owned-floor-20261011-02')
anchor="(ROOT/'prepare.py').write_text(s)"
assert recipe.count(anchor)==1
insert="""anchor = \"plan['pins'] += mapping['runtime_sources']\"
assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+\"rejected_prepare = DIAG / 'transfer-prepared-accepted-source-20261011-01'\\nplan['pins'] += [pin(rejected_prepare / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferPreparedAcceptedSource01.lean', 'project/ShielddSecurity/TransferPreparedAcceptedSource01.lean', 'runs/01-TransferPreparedAcceptedSource01/stdout.txt']]\\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\\n\"+s[pos:]
"""
recipe=recipe.replace(anchor,insert+anchor)
(ROOT/'prepare_recipe.py').write_text(recipe)
print({'fresh_successor':str(ROOT),'contract_changes':0,'rejected_proof_credit':0})
