"""Rename reserved field token only; retain strict failed whole parser attempt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-host-seal-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferHostSeal01.lean').read_text()
assert source.count('  seal : SealBackend')==1 and source.count('io.seal')==9
source=source.replace('  seal : SealBackend','  backend : SealBackend').replace('io.seal','io.backend')
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferHostSeal01.lean').write_text(source)
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-host-seal-owned-floor-20261011-01'"
assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-host-seal-owned-floor-20261011-02'")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
s=s.replace(anchor,"rejected_host_seal = DIAG / 'transfer-host-seal-20261011-01'\nplan['pins'] += [pin(rejected_host_seal / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferHostSeal01.lean', 'project/ShielddSecurity/TransferHostSeal01.lean', 'runs/01-TransferHostSeal01/stdout.txt']]\n"+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Whole strict failed 01 zero credit including compiler placeholders after reserved field seal parse error. Field renamed backend consistently; intended data and actual call flow/contract premises unchanged. Source contains no sorry/admit/axioms. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'reserved_field_parser_rename':True,'rejected_whole_attempt_credit':0})
