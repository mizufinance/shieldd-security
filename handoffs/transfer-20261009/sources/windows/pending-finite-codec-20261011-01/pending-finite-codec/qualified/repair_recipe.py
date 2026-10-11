"""Remove redundant tactics after eta/rewrite already closes coherent erasure proof."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-pending-finite-codec-20261011-01'
s=(old/'handwritten/TransferPendingFiniteCodec01.lean').read_text()
anchor='  rw [members]\n  cases pending\n  rfl'
assert s.count(anchor)==1; s=s.replace(anchor,'  rw [members]')
p=ROOT/'handwritten/TransferPendingFiniteCodec01.lean'; assert not p.exists(); p.parent.mkdir(); p.write_text(s)
recipe=(old/'prepare_recipe.py').read_text().replace('transfer-pending-finite-codec-owned-floor-20261011-01','transfer-pending-finite-codec-owned-floor-20261011-02')
anchor="(ROOT/'prepare.py').write_text(s)"; assert recipe.count(anchor)==1
insert="""anchor = \"plan['pins'] += mapping['runtime_sources']\"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+\"failed_codec = DIAG / 'transfer-pending-finite-codec-20261011-01'\\nplan['pins'] += [pin(failed_codec / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferPendingFiniteCodec01.lean', 'project/ShielddSecurity/TransferPendingFiniteCodec01.lean', 'runs/01-TransferPendingFiniteCodec01/stdout.txt']]\\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\\n\"+s[pos:]
"""
recipe=recipe.replace(anchor,insert+anchor); (ROOT/'prepare_recipe.py').write_text(recipe)
print({'fresh_successor':True,'contract_changes':0,'rejected_proof_credit':0})
