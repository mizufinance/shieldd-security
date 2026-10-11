"""Repair exact authenticated-read receipt; retain rejected whole attempt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-writer-recover-current-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferWriterRecoverCurrent01.lean').read_text()
assert source.count('root, actual, rfl, rfl, same')==1
source=source.replace('root, actual, rfl, rfl, same','root, actual, rfl, actualRead, same')
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferWriterRecoverCurrent01.lean').write_text(source)
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-writer-recover-current-owned-floor-20261011-01'"
assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-writer-recover-current-owned-floor-20261011-02'")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
s=s.replace(anchor,"rejected_current = DIAG / 'transfer-writer-recover-current-20261011-01'\nplan['pins'] += [pin(rejected_current / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferWriterRecoverCurrent01.lean', 'project/ShielddSecurity/TransferWriterRecoverCurrent01.lean', 'runs/01-TransferWriterRecoverCurrent01/stdout.txt']]\n"+anchor)
a="Fresh source composition; prior whole rejected attempts retained with zero credit. No guard changes."
assert s.count(a)==1
s=s.replace(a,'Whole strict failed 01 zero credit including compiler placeholder after actual authenticated read existential receipt required actualRead rather than rfl. Only that proof receipt repaired; all program definitions, conclusions and premises unchanged. Source no sorry/admit/axioms. Guards unchanged.')
(ROOT/'prepare.py').write_text(s)
print({'actual_read_receipt_repaired':True,'rejected_whole_credit':0})
