"""Use reflexivity after split already applies the denied parent gate."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-stage-boundary-source-20261011-01'
s=(old/'handwritten/TransferStageBoundarySource01.lean').read_text()
a='  · exact if_neg denied'; assert s.count(a)==1
s=s.replace(a,'  · rfl')
p=ROOT/'handwritten/TransferStageBoundarySource01.lean'; assert not p.exists(); p.parent.mkdir(); p.write_text(s)
recipe=(old/'prepare_recipe.py').read_text().replace('transfer-stage-boundary-source-owned-floor-20261011-01','transfer-stage-boundary-source-owned-floor-20261011-02')
recipe=recipe.replace('then refuses missing/unavailable parent initialization reads or existing boundary/format/root/legacy nullifier values', 'then requires successfully observed absent initialization data and refuses unavailable reads or existing boundary/format/root/legacy nullifier values')
anchor="(ROOT/'prepare.py').write_text(s)"; assert recipe.count(anchor)==1
insert="""anchor = "plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+"failed_writer = DIAG / 'transfer-stage-boundary-source-20261011-01'\\nplan['pins'] += [pin(failed_writer / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferStageBoundarySource01.lean', 'project/ShielddSecurity/TransferStageBoundarySource01.lean', 'runs/01-TransferStageBoundarySource01/stdout.txt']]\\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\\n"+s[pos:]
"""
recipe=recipe.replace(anchor,insert+anchor); (ROOT/'prepare_recipe.py').write_text(recipe)
print({'program_changes':0,'contract_changes':0,'scope_clarified':'observed absent data allowed; unavailable read refused','rejected_proof_credit':0})
