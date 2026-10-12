from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
prior=DIAG/'transfer-word-stage-numeric-refinement-20261011-01'
s=(prior/'prepare.py').read_text()
needle="POOL = DIAG / 'transfer-word-stage-numeric-refinement-owned-floor-20261011-01'"
assert s.count(needle)==1;s=s.replace(needle,"POOL = DIAG / 'transfer-word-stage-numeric-refinement-owned-floor-20261011-02'")
note=' Initial numeric-refinement attempt stopped at startup on physical pressure after 11.56688s, no stdout or Lean object/audits, zero credit. Exact original preparation/source/plan/events retained; fresh same-source attempt keeps every guard unchanged. No accepted ancestor replay.'
needle="mapping_file = ROOT / 'source-mapping.json'"
assert s.count(needle)==1;s=s.replace(needle,"mapping['scope'] += "+repr(note)+"\nmapping['interfaces'].append("+repr(note)+")\n"+needle)
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"pressureNumeric=DIAG/'transfer-word-stage-numeric-refinement-20261011-01'\nassert not (pressureNumeric/'runs/01-TransferWordStageNumericRefinement01/stdout.txt').exists()\nplan['pins'] += [pin(pressureNumeric/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageNumericRefinement01.lean','project/ShielddSecurity/TransferWordStageNumericRefinement01.lean']]\nplan['source_repairs'] += "+repr(note)+"\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
handwritten=ROOT/'handwritten';handwritten.mkdir(exist_ok=False)
(handwritten/'TransferWordStageNumericRefinement01.lean').write_bytes((prior/'handwritten/TransferWordStageNumericRefinement01.lean').read_bytes())
print({'same_source':True,'pressure_attempt_retained':True,'fresh_reports':6,'limits_unchanged':True})
