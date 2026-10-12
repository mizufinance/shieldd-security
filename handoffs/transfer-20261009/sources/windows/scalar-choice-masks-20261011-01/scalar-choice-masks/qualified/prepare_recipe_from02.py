from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
prior=DIAG/'transfer-scalar-choice-masks-20261012-02'
assert not (prior/'plan.json').exists() and not (prior/'events.jsonl').exists()
s=(prior/'prepare_recipe_from01.py').read_text()
assert s.count('assert len(unrunChoiceFiles)==11')==1
s=s.replace('assert len(unrunChoiceFiles)==11','assert len(unrunChoiceFiles)==10')
needle="plan['pins'].append(pin(ROOT/'prepare_recipe_from01.py'))"
assert s.count(needle)==1
s=s.replace(needle,needle+"\nplan['pins'].append(pin(ROOT/'prepare_recipe_from02.py'))\nfailedChoiceSetup=DIAG/'transfer-scalar-choice-masks-20261012-02'\nfailedChoiceFiles=sorted(p for p in failedChoiceSetup.rglob('*') if p.is_file())\nassert len(failedChoiceFiles)==9 and not (failedChoiceSetup/'plan.json').exists() and not (failedChoiceSetup/'events.jsonl').exists()\nplan['pins'] += [pin(p) for p in failedChoiceFiles]")
(ROOT/'prepare_recipe_from01.py').write_text(s)
subprocess.run([sys.executable,'-B',str(ROOT/'prepare_recipe_from01.py')],check=True)
assert (ROOT/'handwritten/TransferScalarChoiceMasks01.lean').read_bytes()==(prior/'handwritten/TransferScalarChoiceMasks01.lean').read_bytes()
print({'prior_setup_failure_retained_files':9,'same_narrowed_source':True,'all_guards_unchanged':True})
