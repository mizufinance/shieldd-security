"""Rewrite the failed write result before unfolding the interrupted Store."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-persist-intent-source-20261011-01'
s=(old/'handwritten/TransferPersistIntentSource01.lean').read_text()
a='  · simp only [failed, interrupt]'
b='  · change {store with ready := (io.writeIntent (interrupt store) bytes filesystem).succeeded} = interrupt store\n    rw [failed]\n    rfl'
assert s.count(a)==1
s=s.replace(a,b)
p=ROOT/'handwritten/TransferPersistIntentSource01.lean'; assert not p.exists(); p.parent.mkdir(); p.write_text(s)
recipe=(old/'prepare_recipe.py').read_text().replace('transfer-persist-intent-source-owned-floor-20261011-01','transfer-persist-intent-source-owned-floor-20261011-02')
anchor="(ROOT/'prepare.py').write_text(s)"; assert recipe.count(anchor)==1
insert="""anchor = "plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+"failed_writer = DIAG / 'transfer-persist-intent-source-20261011-01'\\nplan['pins'] += [pin(failed_writer / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferPersistIntentSource01.lean', 'project/ShielddSecurity/TransferPersistIntentSource01.lean', 'runs/01-TransferPersistIntentSource01/stdout.txt']]\\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\\n"+s[pos:]
"""
recipe=recipe.replace(anchor,insert+anchor); (ROOT/'prepare_recipe.py').write_text(recipe)
print({'program_changes':0,'contract_changes':0,'rejected_proof_credit':0})
