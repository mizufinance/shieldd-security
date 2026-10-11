"""Repair three case-rewritten receipts; preserve whole rejected attempt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-end-to-end-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferEndToEnd01.lean').read_text()
assert source.count('state, frozen, endCall, sealCall, taken')==1
assert source.count('state, boundary, rebuilt, selected')==1
source=source.replace('state, frozen, endCall, sealCall, taken','state, frozen, rfl, rfl, taken').replace('state, boundary, rebuilt, selected','state, boundary, rfl, selected')
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferEndToEnd01.lean').write_text(source)
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-end-to-end-owned-floor-20261011-01'";assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-end-to-end-owned-floor-20261011-02'")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
s=s.replace(anchor,"rejected_pipeline = DIAG / 'transfer-end-to-end-20261011-01'\nplan['pins'] += [pin(rejected_pipeline / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferEndToEnd01.lean', 'project/ShielddSecurity/TransferEndToEnd01.lean', 'runs/01-TransferEndToEnd01/stdout.txt']]\n"+anchor)
a='Fresh source composition; original failed attempts retained with zero credit. No guard changes.';assert s.count(a)==1
s=s.replace(a,'Whole strict failed 01 zero credit after three case-rewritten receipt type errors and compiler placeholders. Only proof receipts changed to rfl; all data/program definitions, conclusions and premises unchanged. Source no sorry/admit/axioms. Guards unchanged.')
(ROOT/'prepare.py').write_text(s)
print({'case_rewritten_receipts_repaired':3,'rejected_whole_credit':0})
