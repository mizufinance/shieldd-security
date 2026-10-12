from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
prior=DIAG/'transfer-word-stage-admission-20261011-01'
s=(prior/'prepare.py').read_text()
needle="POOL = DIAG / 'transfer-word-stage-admission-owned-floor-20261011-01'"
assert s.count(needle)==1;s=s.replace(needle,"POOL = DIAG / 'transfer-word-stage-admission-owned-floor-20261011-02'")
note=' Original attempt rejected for two constructor-name local-variable lint warnings after 17.939145s. Rename only local unit binders to unitValue; no theorem contract, guard, definition or lint setting change. All original source/plan/complete stdout and any uncredited object retained; entire rejected attempt zero credit including complete reports. Fresh six-audit source attempt; no accepted ancestor replay.'
needle="mapping_file = ROOT / 'source-mapping.json'"
assert s.count(needle)==1;s=s.replace(needle,"mapping['scope'] += "+repr(note)+"\nmapping['interfaces'].append("+repr(note)+")\n"+needle)
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"lintAdmission=DIAG/'transfer-word-stage-admission-20261011-01'\nplan['pins'] += [pin(lintAdmission/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageAdmission01.lean','project/ShielddSecurity/TransferWordStageAdmission01.lean','runs/01-TransferWordStageAdmission01/stdout.txt']]\nlintObject=lintAdmission/'project/ShielddSecurity/TransferWordStageAdmission01.olean'\nassert lintObject.is_file()\nplan['pins'].append(pin(lintObject))\nplan['source_repairs'] += "+repr(note)+"\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
handwritten=ROOT/'handwritten';handwritten.mkdir(exist_ok=False)
source=(prior/'handwritten/TransferWordStageAdmission01.lean').read_text()
assert source.count('| ok unit =>')==2 and source.count('cases unit\n')==2
source=source.replace('| ok unit =>','| ok unitValue =>').replace('cases unit\n','cases unitValue\n')
(handwritten/'TransferWordStageAdmission01.lean').write_text(source)
print({'local_variable_lint_repair':True,'original_attempt_retained':True,'fresh_reports':6,'limits_and_lint_unchanged':True})
