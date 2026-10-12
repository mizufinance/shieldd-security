from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-endpoint-20261012-05'
assert not (ROOT/'assemble.py').exists() and not (OLD/'manifest.json').exists()
s=(OLD/'assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-scalar-pow-field-20261012-04'","CURRENT = DIAG / 'transfer-scalar-pow-field-20261012-05'").replace("CHECKPOINT = DIAG / 'transfer-scalar-pow-field-checkpoint-20261012-04'","CHECKPOINT = DIAG / 'transfer-scalar-pow-field-checkpoint-20261012-05'")
old="else:names+=['events.jsonl','runs/01-TransferScalarPowField01/stdout.txt']"
new="""elif attempt==2:names+=['events.jsonl','runs/01-TransferScalarPowField01/stdout.txt']
    else:
        names.append('events.jsonl')
        priorStdout=prior/'runs/01-TransferScalarPowField01/stdout.txt'
        assert not priorStdout.exists()
"""
assert s.count(old)==1;s=s.replace(old,new).replace('for attempt in [1,2,3]:','for attempt in [1,2,3,4]:')
s=s.replace('Original29 prior raw artifacts','Original39 prior raw artifacts')
at=s.index("add(Path(__file__), 'assemble.py'")
extra="for name in ['prepare_assembly.py','assemble.py']:\n    add(DIAG/'transfer-scalar-pow-field-endpoint-20261012-05'/name,'prior-unrun-assembly05/'+name,'original unrun assembly derivation preserved unchanged')\n"
s=s[:at]+extra+s[at:]
s=s.replace("'rejected_attempts': 1, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0","'rejected_attempts': 2, 'withdrawn_unrun_sources': 2, 'unprepared_setup_failures': 0")
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-pow-field-checkpoint-20261012-05';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'whole_owned_modules':204,'inherited_complete_reports':1428,'fresh_theorems':6,'prior_raw_producer_files':39,'pressure_predecessor_stdout_absent':True,'source_theorems_and_guards_unchanged':True})
