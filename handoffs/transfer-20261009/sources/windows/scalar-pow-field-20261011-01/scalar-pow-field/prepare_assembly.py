from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-endpoint-20261012-07'
assert not (ROOT/'assemble.py').exists() and not (OLD/'manifest.json').exists()
s=(OLD/'assemble.py').read_text().replace("CURRENT = DIAG / 'transfer-scalar-pow-field-20261012-07'","CURRENT = DIAG / 'transfer-scalar-pow-field-20261012-08'").replace("CHECKPOINT = DIAG / 'transfer-scalar-pow-field-checkpoint-20261012-07'","CHECKPOINT = DIAG / 'transfer-scalar-pow-field-checkpoint-20261012-08'")
s=s.replace('for attempt in [1,2,3,4,5,6]:','for attempt in [1,2,3,4,5,6,7]:').replace('Original56 prior raw producer/composition artifacts','Original66 prior raw producer/composition artifacts')
s=s.replace("'rejected_attempts': 2, 'withdrawn_unrun_sources': 3","'rejected_attempts': 3, 'withdrawn_unrun_sources': 3")
at=s.index("add(Path(__file__), 'assemble.py'")
extra="for name in ['prepare_assembly.py','assemble.py']:\n    add(DIAG/'transfer-scalar-pow-field-endpoint-20261012-07'/name,'prior-unrun-assembly07/'+name,'original unrun assembly derivation preserved unchanged')\n"
s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-pow-field-checkpoint-20261012-08';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'whole_owned_modules':163,'inherited_complete_reports':1296,'fresh_theorems':6,'prior_raw_artifacts':66,'assembly_not_run':True})
