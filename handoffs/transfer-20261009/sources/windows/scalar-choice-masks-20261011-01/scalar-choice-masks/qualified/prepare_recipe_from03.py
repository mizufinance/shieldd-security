from pathlib import Path
import subprocess,sys,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-scalar-choice-masks-20261012-03'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(s) for s in (prior/'events.jsonl').read_text().splitlines()]
assert events[-1]['result']['status']=='failed' and events[-1]['result']['reason']=='Physical memory pressure'
assert not (prior/'runs/01-TransferScalarChoiceMasks01/stdout.txt').exists()
assert not list((prior/'project/ShielddSecurity').glob('*.olean'))
(ROOT/'prepare_recipe_from02.py').write_bytes((prior/'prepare_recipe_from02.py').read_bytes())
subprocess.run([sys.executable,'-B',str(ROOT/'prepare_recipe_from02.py')],check=True)
s=(ROOT/'prepare.py').read_text()
extra="""plan['pins'].append(pin(ROOT/'prepare_recipe_from03.py'))
pressureChoice=DIAG/'transfer-scalar-choice-masks-20261012-03'
pressureFiles=sorted(p for p in pressureChoice.rglob('*') if p.is_file())
assert len(pressureFiles)==13 and not (pressureChoice/'runs/01-TransferScalarChoiceMasks01/stdout.txt').exists()
plan['pins'] += [pin(p) for p in pressureFiles]
priorChoiceEndpoint=DIAG/'transfer-scalar-choice-masks-endpoint-20261012-03'
plan['pins'] += [pin(priorChoiceEndpoint/n) for n in ['prepare_assembly.py','assemble.py']]
priorChoiceCheckpoint=DIAG/'transfer-scalar-choice-masks-checkpoint-20261012-03'
plan['pins'] += [pin(priorChoiceCheckpoint/n) for n in ['preservation_check.py','preservation.json']]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_text(s)
assert (ROOT/'handwritten/TransferScalarChoiceMasks01.lean').read_bytes()==(prior/'handwritten/TransferScalarChoiceMasks01.lean').read_bytes()
print({'prior_memory_admission_failure_retained':True,'no_prior_Lean_stdout_or_object':True,'same_narrowed_source':True,'all_guards_unchanged':True})
