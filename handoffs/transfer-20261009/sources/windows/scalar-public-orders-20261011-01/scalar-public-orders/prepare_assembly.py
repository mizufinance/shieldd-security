from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-public-orders-endpoint-20261012-03/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-scalar-public-orders-20261012-03'","CURRENT = DIAG / 'transfer-scalar-public-orders-20261012-04'")
s=s.replace("CHECKPOINT = DIAG / 'transfer-scalar-public-orders-checkpoint-20261012-03'","CHECKPOINT = DIAG / 'transfer-scalar-public-orders-checkpoint-20261012-04'")
s=s.replace("'rejected_attempts': 1","'rejected_attempts': 2")
extra="""row=pin(CURRENT/'prepare_recipe_from03.py');assert row in plan['pins']
add(CURRENT/'prepare_recipe_from03.py','qualified/prepare_recipe_from03.py','one redundant decide command removed; all statements and guards unchanged')
prior=DIAG/'transfer-scalar-public-orders-20261012-03'
events03=[json.loads(line) for line in (prior/'events.jsonl').read_text().splitlines()]
assert events03[-1]['result']['reason']=='Lean exit 1'
for path in sorted(prior.rglob('*')):
    if path.is_file():
        row=pin(path);assert row in plan['pins']
        add(path,'history/failed-source03/'+path.relative_to(prior).as_posix(),'exact original failed Lean source/full reports, not a successful semantic control')
priorEndpoint=DIAG/'transfer-scalar-public-orders-endpoint-20261012-03'
for name in ['prepare_assembly.py','assemble.py']:
    path=priorEndpoint/name;assert pin(path) in plan['pins']
    add(path,'history/unrun-endpoint03/'+name,'exact original unrun assembly source retained')
priorCheckpoint=DIAG/'transfer-scalar-public-orders-checkpoint-20261012-03/preservation_check.py'
assert pin(priorCheckpoint) in plan['pins']
add(priorCheckpoint,'history/unrun-checkpoint03/preservation_check.py','exact original unrun checkpoint recipe retained')
"""
at=s.index("add(Path(__file__), 'assemble.py'");s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-public-orders-checkpoint-20261012-04';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_theorems':7,'full_failed02_and03_outputs_retained':True,'assembly_not_run':True})
