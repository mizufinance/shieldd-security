from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
prior=DIAG/'transfer-checked-word-stage-refinement-20261011-01'
s=(prior/'prepare.py').read_text()
needle="POOL = DIAG / 'transfer-checked-word-stage-refinement-owned-floor-20261011-01'"
assert s.count(needle)==1;s=s.replace(needle,"POOL = DIAG / 'transfer-checked-word-stage-refinement-owned-floor-20261011-02'")
note=' First checked-stage refinement Lean exit1 after22.1859879s because proof-local reader/numeric helper calls on Sum.inl did not determine phantom Other type. Add explicit existing Other type arguments only, no definition/contract/limit change. Complete original error/sorryAx reports retained with entire attempt zero credit; fresh eight-audit attempt and no accepted ancestor replay.'
needle="mapping_file = ROOT / 'source-mapping.json'"
assert s.count(needle)==1;s=s.replace(needle,"mapping['scope'] += "+repr(note)+"\nmapping['interfaces'].append("+repr(note)+")\n"+needle)
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"failedChecked=DIAG/'transfer-checked-word-stage-refinement-20261011-01'\nplan['pins'] += [pin(failedChecked/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordStageRefinement01.lean','project/ShielddSecurity/TransferCheckedWordStageRefinement01.lean','runs/01-TransferCheckedWordStageRefinement01/stdout.txt']]\nplan['source_repairs'] += "+repr(note)+"\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
handwritten=ROOT/'handwritten';handwritten.mkdir(exist_ok=False)
source=(prior/'handwritten/TransferCheckedWordStageRefinement01.lean').read_text()
source=source.replace('readerForPrevious (backend.readerGate child)','readerForPrevious (Other := Other) (backend.readerGate child)').replace('checkedNumericStage backend child','checkedNumericStage (Other := Other) backend child')
(handwritten/'TransferCheckedWordStageRefinement01.lean').write_text(source)
print({'explicit_phantom_type_repair':True,'original_attempt_retained':True,'fresh_reports':8,'limits_and_contracts_unchanged':True})
