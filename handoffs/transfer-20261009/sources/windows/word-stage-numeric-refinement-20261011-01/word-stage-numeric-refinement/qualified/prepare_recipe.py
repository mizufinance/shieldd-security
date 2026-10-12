from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
prior=DIAG/'transfer-word-stage-numeric-refinement-20261011-02'
s=(prior/'prepare.py').read_text()
needle="POOL = DIAG / 'transfer-word-stage-numeric-refinement-owned-floor-20261011-02'"
assert s.count(needle)==1;s=s.replace(needle,"POOL = DIAG / 'transfer-word-stage-numeric-refinement-owned-floor-20261011-03'")
note=' Second attempt Lean exit1 after18.1735478s: unavailable Bool.true_eq_true spelling, redundant branch-case simp equations, and already-rewritten existential witness equation. Repair only proof search by removing unavailable/redundant simp arguments and using rfl for rewritten witness. Complete original error/warning/axiom output retained, including sorryAx diagnostics with zero credit for entire failed attempt. Definitions/contracts/all resource/lint limits unchanged.'
needle="mapping_file = ROOT / 'source-mapping.json'"
assert s.count(needle)==1;s=s.replace(needle,"mapping['scope'] += "+repr(note)+"\nmapping['interfaces'].append("+repr(note)+")\n"+needle)
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"failedNumeric=DIAG/'transfer-word-stage-numeric-refinement-20261011-02'\nplan['pins'] += [pin(failedNumeric/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageNumericRefinement01.lean','project/ShielddSecurity/TransferWordStageNumericRefinement01.lean','runs/01-TransferWordStageNumericRefinement01/stdout.txt']]\nplan['source_repairs'] += "+repr(note)+"\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
handwritten=ROOT/'handwritten';handwritten.mkdir(exist_ok=False)
source=(prior/'handwritten/TransferWordStageNumericRefinement01.lean').read_text()
source=source.replace(', Bool.true_eq_true','').replace('unique, Bool.false_eq_true','Bool.false_eq_true').replace('unique, if_true','if_true').replace('fresh, Bool.false_eq_true','Bool.false_eq_true').replace('fresh, if_true','if_true').replace('unspent, Bool.false_eq_true','Bool.false_eq_true')
source=source.replace('simp only [Bool.false_eq_true, if_false]; rfl','simp only [Bool.false_eq_true, if_false] <;> rfl')
assert source.count('exact ⟨next, inspected, nextEq.trans')==1
source=source.replace('exact ⟨next, inspected, nextEq.trans','exact ⟨next, rfl, nextEq.trans')
(handwritten/'TransferWordStageNumericRefinement01.lean').write_text(source)
print({'proof_search_and_rewritten_witness_repair':True,'original_attempts_retained':True,'fresh_reports':6,'limits_and_contracts_unchanged':True})
