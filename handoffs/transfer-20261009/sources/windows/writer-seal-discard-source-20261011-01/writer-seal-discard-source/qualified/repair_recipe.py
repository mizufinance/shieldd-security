"""Remove unnecessary simpa; retain strict lint gate and zero credit for predecessor."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-writer-seal-discard-source-20261011-01'
s=(old/'handwritten/TransferWriterSealDiscardSource01.lean').read_text()
anchor='by simpa only [interrupted, committed]'; assert s.count(anchor)==1
s=s.replace(anchor,'by simp only [interrupted, committed]')
p=ROOT/'handwritten/TransferWriterSealDiscardSource01.lean'; assert not p.exists(); p.parent.mkdir(); p.write_text(s)
recipe=(old/'prepare_recipe.py').read_text().replace('transfer-writer-seal-discard-source-owned-floor-20261011-01','transfer-writer-seal-discard-source-owned-floor-20261011-02')
anchor="(ROOT/'prepare.py').write_text(s)"; assert recipe.count(anchor)==1
insert="""anchor = \"plan['pins'] += mapping['runtime_sources']\"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+\"failed_seal_discard = DIAG / 'transfer-writer-seal-discard-source-20261011-01'\\nplan['pins'] += [pin(failed_seal_discard / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferWriterSealDiscardSource01.lean', 'project/ShielddSecurity/TransferWriterSealDiscardSource01.lean', 'runs/01-TransferWriterSealDiscardSource01/stdout.txt']]\\nfailed_object = failed_seal_discard / 'project/ShielddSecurity/TransferWriterSealDiscardSource01.olean'\\nif failed_object.exists(): plan['pins'].append(pin(failed_object))\\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\\n\"+s[pos:]
"""
recipe=recipe.replace(anchor,insert+anchor); (ROOT/'prepare_recipe.py').write_text(recipe)
print({'proof_only_lint_repair':True,'contract_changes':0,'strict_lint_unchanged':True,'rejected_proof_credit':0})
