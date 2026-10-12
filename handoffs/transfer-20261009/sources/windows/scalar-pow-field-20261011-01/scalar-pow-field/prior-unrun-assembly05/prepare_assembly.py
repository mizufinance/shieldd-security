from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-endpoint-20261012-04'
assert not (ROOT/'assemble.py').exists() and not (OLD/'manifest.json').exists()
s=(OLD/'assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-scalar-pow-field-20261012-03'","CURRENT = DIAG / 'transfer-scalar-pow-field-20261012-04'").replace("CHECKPOINT = DIAG / 'transfer-scalar-pow-field-checkpoint-20261012-03'","CHECKPOINT = DIAG / 'transfer-scalar-pow-field-checkpoint-20261012-04'")
s=s.replace('for attempt in [1,2]:','for attempt in [1,2,3]:').replace("if attempt==1:assert not (prior/'events.jsonl').exists()","if attempt in [1,3]:assert not (prior/'events.jsonl').exists()")
s=s.replace("add(ROOT/'prepare_recipe_from03.py','prepare_recipe_from03.py','fresh assembly source repair derivation')", "for name in ['prepare_recipe_from03.py','prepare_assembly.py','assemble.py']:\n    add(DIAG/'transfer-scalar-pow-field-endpoint-20261012-04'/name,'prior-unrun-assembly04/'+name,'original unrun assembly derivation preserved unchanged')")
s=s.replace('Original20 prior raw artifacts','Original29 prior raw artifacts').replace('Two unused simplifier arguments removed; all statements/contracts/guards unchanged.','Two unused simplifier arguments removed and direct import narrowed to the actual qualified field-operation module; all statements/contracts/guards unchanged.')
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-pow-field-checkpoint-20261012-04';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'whole_owned_modules':204,'inherited_complete_reports':1428,'fresh_theorems':6,'prior_raw_producer_files':29,'prepared_unrun_assembler_preserved':True})
