"""Normalize record layout and explicit missing-height contradiction; strict lints retained."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-boundary-reader-source-20261011-01'
s=(old/'handwritten/TransferBoundaryReaderSource01.lean').read_text()
changes=[
('  {stage with available := io.available, readPrevious := readBoundary io project,\n    format := formatValueBytes, commitment := io.commitment}', '  {stage with available := io.available, readPrevious := readBoundary io project, format := formatValueBytes, commitment := io.commitment}'),
('simp only [Option.bind_some, if_neg denied]', 'simp only [Option.bind_some]'),
('| none => cases noninitial', '| none =>\n      have empty : prepared.previous.height.isSome = false := by rw [height]; rfl\n      exact Bool.noConfusion (empty.symm.trans noninitial)')]
for a,b in changes:
    assert s.count(a)==1,a
    s=s.replace(a,b)
p=ROOT/'handwritten/TransferBoundaryReaderSource01.lean'; assert not p.exists(); p.parent.mkdir(); p.write_text(s)
recipe=(old/'prepare_recipe.py').read_text().replace('transfer-boundary-reader-source-owned-floor-20261011-01','transfer-boundary-reader-source-owned-floor-20261011-02')
anchor="(ROOT/'prepare.py').write_text(s)"; assert recipe.count(anchor)==1
insert="""anchor = "plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+"failed_writer = DIAG / 'transfer-boundary-reader-source-20261011-01'\\nplan['pins'] += [pin(failed_writer / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferBoundaryReaderSource01.lean', 'project/ShielddSecurity/TransferBoundaryReaderSource01.lean', 'runs/01-TransferBoundaryReaderSource01/stdout.txt']]\\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\\n"+s[pos:]
"""
recipe=recipe.replace(anchor,insert+anchor); (ROOT/'prepare_recipe.py').write_text(recipe)
print({'layout_change':True,'contract_changes':0,'rejected_proof_credit':0})
