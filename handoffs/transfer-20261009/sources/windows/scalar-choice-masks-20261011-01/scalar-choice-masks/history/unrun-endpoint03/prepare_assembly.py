from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-choice-masks-endpoint-20261012-01/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-scalar-choice-masks-20261012-01'","CURRENT = DIAG / 'transfer-scalar-choice-masks-20261012-03'")
s=s.replace("CHECKPOINT = DIAG / 'transfer-scalar-choice-masks-checkpoint-20261012-01'","CHECKPOINT = DIAG / 'transfer-scalar-choice-masks-checkpoint-20261012-03'")
s=s.replace("'rejected_attempts': 0, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0","'rejected_attempts': 0, 'withdrawn_unrun_sources': 1, 'unprepared_setup_failures': 1")
extra="""for name in ['prepare_recipe_from01.py','prepare_recipe_from02.py']:
    row=pin(CURRENT/name);assert row in plan['pins']
    add(CURRENT/name,'qualified/'+name,'exact source preparation; original import narrowed only, fixed guards unchanged')
for attempt,expected in [(1,10),(2,9)]:
    prior=DIAG/('transfer-scalar-choice-masks-20261012-%02d'%attempt)
    files=sorted(p for p in prior.rglob('*') if p.is_file())
    assert len(files)==expected and not (prior/'events.jsonl').exists()
    for path in files:
        row=pin(path);assert row in plan['pins']
        add(path,'history/source-%02d/'%attempt+path.relative_to(prior).as_posix(),'exact retained unrun/setup original; not a successful semantic control')
priorEndpoint=DIAG/'transfer-scalar-choice-masks-endpoint-20261012-01'
for name in ['prepare_assembly.py','assemble.py']:
    row=pin(priorEndpoint/name);assert row in plan['pins']
    add(priorEndpoint/name,'history/unrun-endpoint01/'+name,'original unrun assembler preserved')
priorCheckpoint=DIAG/'transfer-scalar-choice-masks-checkpoint-20261012-01/preservation_check.py'
assert pin(priorCheckpoint) in plan['pins']
add(priorCheckpoint,'history/unrun-checkpoint01/preservation_check.py','original unrun checkpoint recipe preserved')
"""
at=s.index("add(Path(__file__), 'assemble.py'");s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-choice-masks-checkpoint-20261012-03';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_public_declarations':20,'original_unrun_files':10,'setup_failed_files':9,'all_guards_unchanged':True,'assembly_not_run':True})
