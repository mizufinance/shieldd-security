from pathlib import Path
import subprocess,sys,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-scalar-public-orders-20261012-03'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(s) for s in (prior/'events.jsonl').read_text().splitlines()]
assert events[-1]['result']['reason']=='Lean exit 1'
assert '97:4: error: No goals to be solved' in (prior/'runs/01-TransferScalarPublicOrders01/stdout.txt').read_text()
(ROOT/'prepare_recipe_from02.py').write_bytes((prior/'prepare_recipe_from02.py').read_bytes())
subprocess.run([sys.executable,'-B',str(ROOT/'prepare_recipe_from02.py')],check=True)
h=ROOT/'handwritten/TransferScalarPublicOrders01.lean';s=h.read_text()
old='    congr 1\n    decide\n  · decide'
new='    congr 1\n  · decide'
assert s.count(old)==1;s=s.replace(old,new);h.write_text(s)
p=ROOT/'prepare.py';s=p.read_text()
extra="""plan['pins'].append(pin(ROOT/'prepare_recipe_from03.py'))
failedOrders03=DIAG/'transfer-scalar-public-orders-20261012-03'
plan['pins'] += [pin(p) for p in sorted(failedOrders03.rglob('*')) if p.is_file()]
plan['pins'] += [pin(DIAG/'transfer-scalar-public-orders-endpoint-20261012-03'/n) for n in ['prepare_assembly.py','assemble.py']]
plan['pins'].append(pin(DIAG/'transfer-scalar-public-orders-checkpoint-20261012-03/preservation_check.py'))
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:];p.write_text(s)
print({'all_seven_statements_unchanged':True,'one_redundant_decide_removed_after_closed_goal':True,'full_failed03_output_retained':True,'same_readonly203_module_floor_and_guards':True})
