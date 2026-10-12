from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-choice-masks-endpoint-20261012-03/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-scalar-choice-masks-20261012-03'","CURRENT = DIAG / 'transfer-scalar-choice-masks-20261012-04'")
s=s.replace("CHECKPOINT = DIAG / 'transfer-scalar-choice-masks-checkpoint-20261012-03'","CHECKPOINT = DIAG / 'transfer-scalar-choice-masks-checkpoint-20261012-04'")
s=s.replace("'rejected_attempts': 0","'rejected_attempts': 1")
extra="""row=pin(CURRENT/'prepare_recipe_from03.py');assert row in plan['pins']
add(CURRENT/'prepare_recipe_from03.py','qualified/prepare_recipe_from03.py','fresh same-source plan, prior memory admission failure retained')
prior=DIAG/'transfer-scalar-choice-masks-20261012-03'
priorEvents=[json.loads(line) for line in (prior/'events.jsonl').read_text().splitlines()]
assert priorEvents[-1]['result']['reason']=='Physical memory pressure'
assert not (prior/'runs/01-TransferScalarChoiceMasks01/stdout.txt').exists()
assert not list((prior/'project/ShielddSecurity').glob('*.olean'))
files=sorted(p for p in prior.rglob('*') if p.is_file());assert len(files)==13
for path in files:
    row=pin(path);assert row in plan['pins']
    add(path,'history/memory-admission-source03/'+path.relative_to(prior).as_posix(),'exact original failed memory admission, no Lean stdout/object; not a successful semantic control')
for label,directory,names in [
    ('unrun-endpoint03','transfer-scalar-choice-masks-endpoint-20261012-03',['prepare_assembly.py','assemble.py']),
    ('checkpoint03','transfer-scalar-choice-masks-checkpoint-20261012-03',['preservation_check.py','preservation.json'])]:
    for name in names:
        path=DIAG/directory/name;assert pin(path) in plan['pins']
        add(path,'history/'+label+'/'+name,'original unrun assembly/preservation data retained')
"""
at=s.index("add(Path(__file__), 'assemble.py'");s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-choice-masks-checkpoint-20261012-04';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_declarations':20,'original_memory_admission_failure_retained':True,'same_source_and_guards':True,'assembly_not_run':True})
