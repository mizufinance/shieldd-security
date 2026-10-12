from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'repair_recipe.py').exists()
s=(DIAG/'transfer-checked-word-stage-refinement-20261011-03/prepare_recipe.py').read_text()
s=s.replace("transfer-checked-word-stage-refinement-owned-floor-20261011-03'","transfer-checked-word-stage-refinement-owned-floor-20261011-04'")
s=s.replace("source.count('      unfold stageFields checkedNumericStage\\n')","source.count('\\n      unfold stageFields checkedNumericStage\\n')")
s=s.replace("source.replace('      unfold stageFields checkedNumericStage\\n','      unfold stageFields checkedNumericStage\\n      dsimp only\\n')","source.replace('\\n      unfold stageFields checkedNumericStage\\n','\\n      unfold stageFields checkedNumericStage\\n      dsimp only\\n')")
needle="at=s.index(\"plan['artifact_policy'] = \")"
assert s.count(needle)==1
s=s.replace(needle,needle+"\nsetup_note=' Third setup source-recipe indentation assertion stopped before plan/Lean, original two setup recipe files retained UNRUN with zero credit; correct only newline-anchored source transformation in fresh fourth root.'\ns=s.replace(\"mapping_file = ROOT / 'source-mapping.json'\",\"mapping['scope'] += \"+repr(setup_note)+\"\\n\"+\"mapping_file = ROOT / 'source-mapping.json'\")\nat=s.index(\"plan['artifact_policy'] = \")\ns=s[:at]+\"unrunChecked=DIAG/'transfer-checked-word-stage-refinement-20261011-03'\\nassert not (unrunChecked/'plan.json').exists() and not (unrunChecked/'events.jsonl').exists()\\nplan['pins'] += [pin(unrunChecked/n) for n in ['prepare_recipe.py','prepare.py']]\\n\"+s[at:]\nat=s.index(\"plan['artifact_policy'] = \")")
(ROOT/'repair_recipe.py').write_text(s)
print({'fresh_fourth_setup':True,'unrun_indentation_assertion_retained':True,'guards_unchanged':True})
