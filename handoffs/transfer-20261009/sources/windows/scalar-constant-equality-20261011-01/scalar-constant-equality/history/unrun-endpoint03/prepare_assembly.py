from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-constant-equality-endpoint-20261012-02/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-scalar-constant-equality-20261012-02'","CURRENT = DIAG / 'transfer-scalar-constant-equality-20261012-03'")
s=s.replace("CHECKPOINT = DIAG / 'transfer-scalar-constant-equality-checkpoint-20261012-02'","CHECKPOINT = DIAG / 'transfer-scalar-constant-equality-checkpoint-20261012-03'")
s=s.replace("'withdrawn_unrun_sources': 0","'withdrawn_unrun_sources': 1")
extra="""row=pin(CURRENT/'prepare_recipe_from02.py');assert row in plan['pins']
add(CURRENT/'prepare_recipe_from02.py','qualified/prepare_recipe_from02.py','exact source import narrowing; declaration bodies and fixed guards unchanged')
prior=DIAG/'transfer-scalar-constant-equality-20261012-02'
assert not (prior/'events.jsonl').exists()
for path in sorted(prior.rglob('*')):
    if path.is_file():
        row=pin(path);assert row in plan['pins']
        add(path,'history/unrun-source02/'+path.relative_to(prior).as_posix(),'exact original prepared unrun source, not a successful semantic control')
priorEndpoint=DIAG/'transfer-scalar-constant-equality-endpoint-20261012-02'
for name in ['prepare_assembly.py','assemble.py']:
    row=pin(priorEndpoint/name);assert row in plan['pins']
    add(priorEndpoint/name,'history/unrun-endpoint02/'+name,'exact original unrun assembly source')
priorCheckpoint=DIAG/'transfer-scalar-constant-equality-checkpoint-20261012-02/preservation_check.py'
assert pin(priorCheckpoint) in plan['pins']
add(priorCheckpoint,'history/unrun-checkpoint02/preservation_check.py','original unrun checkpoint recipe')
"""
at=s.index("add(Path(__file__), 'assemble.py'");s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-constant-equality-checkpoint-20261012-03';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_public_declarations':12,'all_original_unrun_and_failed_setup_files_retained':True,'all_guards_unchanged':True,'assembly_not_run':True})
