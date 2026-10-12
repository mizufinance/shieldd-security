from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
prior=DIAG/'transfer-checked-word-stage-refinement-20261011-02'
s=(prior/'prepare.py').read_text()
needle="POOL = DIAG / 'transfer-checked-word-stage-refinement-owned-floor-20261011-02'"
assert s.count(needle)==1;s=s.replace(needle,"POOL = DIAG / 'transfer-checked-word-stage-refinement-owned-floor-20261011-03'")
note=' Second checked-stage attempt Lean exit1 after18.2141371s: local numeric keys let remained opaque to case rewriting, including repeated pure uniqueness inside sealed inspection. Normalize proof-local lets and sealed inspection projections before case analysis; definitions/eight contracts/all guards unchanged. Complete original errors/warning/sorryAx reports retained with entire failed attempt zero credit; no accepted ancestor replay.'
needle="mapping_file = ROOT / 'source-mapping.json'"
assert s.count(needle)==1;s=s.replace(needle,"mapping['scope'] += "+repr(note)+"\nmapping['interfaces'].append("+repr(note)+")\n"+needle)
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"failedCheckedSecond=DIAG/'transfer-checked-word-stage-refinement-20261011-02'\nplan['pins'] += [pin(failedCheckedSecond/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordStageRefinement01.lean','project/ShielddSecurity/TransferCheckedWordStageRefinement01.lean','runs/01-TransferCheckedWordStageRefinement01/stdout.txt']]\nplan['source_repairs'] += "+repr(note)+"\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
handwritten=ROOT/'handwritten';handwritten.mkdir(exist_ok=False)
source=(prior/'handwritten/TransferCheckedWordStageRefinement01.lean').read_text()
assert source.count('      unfold checkedNumericStage\n')==1
source=source.replace('      unfold checkedNumericStage\n','      unfold checkedNumericStage\n      dsimp only\n')
assert source.count('      unfold stageFields checkedNumericStage\n')==1
source=source.replace('      unfold stageFields checkedNumericStage\n','      unfold stageFields checkedNumericStage\n      dsimp only\n')
assert source.count('        unfold stageFields checkedNumericStage\n')==1
source=source.replace('        unfold stageFields checkedNumericStage\n','        unfold stageFields checkedNumericStage\n        dsimp only [checkedObject, inspect, previousPending, projectObjectPending, decodeNative, decodeWordPending, restore]\n')
(handwritten/'TransferCheckedWordStageRefinement01.lean').write_text(source)
print({'proof_local_let_normalization_repair':True,'original_attempts_retained':True,'fresh_reports':8,'limits_and_contracts_unchanged':True})
