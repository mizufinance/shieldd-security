from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-constant-equality-endpoint-20261012-03/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-scalar-constant-equality-20261012-03'","CURRENT = DIAG / 'transfer-scalar-constant-equality-20261012-04'")
s=s.replace("CHECKPOINT = DIAG / 'transfer-scalar-constant-equality-checkpoint-20261012-03'","CHECKPOINT = DIAG / 'transfer-scalar-constant-equality-checkpoint-20261012-04'")
s=s.replace("'rejected_attempts': 0","'rejected_attempts': 1")
old="add(row['path'],'runtime/Cargo.lock','exact locked runtime dependency checksum authority')"
assert s.count(old)==1
s=s.replace(old,"assert row in mapping['runtime_sources']  # Exact authority archived once by the existing runtime loop.")
extra="""row=pin(CURRENT/'prepare_recipe_from03.py');assert row in plan['pins']
add(CURRENT/'prepare_recipe_from03.py','qualified/prepare_recipe_from03.py','source-only proof repair; all twelve statements and execution guards unchanged')
prior=DIAG/'transfer-scalar-constant-equality-20261012-03'
events03=[json.loads(line) for line in (prior/'events.jsonl').read_text().splitlines()]
assert events03[-1]['result']['reason']=='Lean exit 1'
for path in sorted(prior.rglob('*')):
    if path.is_file():
        row=pin(path);assert row in plan['pins']
        add(path,'history/failed-source03/'+path.relative_to(prior).as_posix(),'exact original failed Lean source and full raw reports; not a successful semantic control')
for label,directory,names in [
    ('unrun-endpoint03','transfer-scalar-constant-equality-endpoint-20261012-03',['prepare_assembly.py','assemble.py']),
    ('checkpoint03','transfer-scalar-constant-equality-checkpoint-20261012-03',['preservation_check.py','preservation.json'])]:
    for name in names:
        path=DIAG/directory/name;assert pin(path) in plan['pins']
        add(path,'history/'+label+'/'+name,'exact original unrun assembly/preservation data retained')
"""
at=s.index("add(Path(__file__), 'assemble.py'");s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-constant-equality-checkpoint-20261012-04';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_declarations':12,'failed03_full_reports_retained':True,'exact_runtime_Cargo_lock_once':True,'assembly_not_run':True})
