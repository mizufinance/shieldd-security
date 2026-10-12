from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-public-orders-endpoint-20261012-02/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-scalar-public-orders-20261012-02'","CURRENT = DIAG / 'transfer-scalar-public-orders-20261012-03'")
s=s.replace("CHECKPOINT = DIAG / 'transfer-scalar-public-orders-checkpoint-20261012-02'","CHECKPOINT = DIAG / 'transfer-scalar-public-orders-checkpoint-20261012-03'")
s=s.replace("'rejected_attempts': 0","'rejected_attempts': 1")
extra="""row=pin(CURRENT/'prepare_recipe_from02.py');assert row in plan['pins']
add(CURRENT/'prepare_recipe_from02.py','qualified/prepare_recipe_from02.py','explicit theorem element argument repair, all seven statements and guards unchanged')
prior=DIAG/'transfer-scalar-public-orders-20261012-02'
events02=[json.loads(line) for line in (prior/'events.jsonl').read_text().splitlines()]
assert events02[-1]['result']['reason']=='Lean exit 1'
for path in sorted(prior.rglob('*')):
    if path.is_file():
        row=pin(path);assert row in plan['pins']
        add(path,'history/failed-source02/'+path.relative_to(prior).as_posix(),'exact original failed Lean source/full reports, not a successful semantic control')
for label,directory,names in [
    ('unrun-endpoint02','transfer-scalar-public-orders-endpoint-20261012-02',['prepare_assembly.py','assemble.py']),
    ('checkpoint02','transfer-scalar-public-orders-checkpoint-20261012-02',['preservation_check.py','preservation.json'])]:
    for name in names:
        path=DIAG/directory/name;assert pin(path) in plan['pins']
        add(path,'history/'+label+'/'+name,'exact original unrun assembly/preservation data retained')
"""
at=s.index("add(Path(__file__), 'assemble.py'");s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-public-orders-checkpoint-20261012-03';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_theorems':7,'full_failed02_output_retained':True,'same_qualified203_module_prime_inverse_pool':True,'assembly_not_run':True})
