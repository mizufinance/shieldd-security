"""Fresh successor with the qualified owned transitive import closure present."""
import ast
import hashlib
import json
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-torsion-euler-20261010-02'
T3 = DIAG / 'transfer-torsion-cardinality49-20261010-03'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
events = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines()]
finished = [e for e in events if e['event'] == 'attempt_finished']
assert len(finished) == 2 and finished[0]['result']['status'] == 'passed' and finished[1]['result']['status'] == 'failed'
assert 'Range.olean' in (PRIOR / 'runs/02-TorsionEulerInteger49/stdout.txt').read_text()
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
t3plan = json.loads((T3 / 'plan.json').read_text())
base = []
originals = plan['owned_imports'] + t3plan['owned_imports'] + finished[0]['result']['objects']
for p in originals:
    assert pin(p['path']) == p
    dest = project / Path(p['path']).name; shutil.copyfile(p['path'], dest); base.append(pin(dest))
assert {Path(p['path']).stem for p in base} == {'CurveCardinalityWindow01', 'SpendGateInputs', 'Range', 'NatModularPower01'}
target = plan['targets'][1]
source = Path(target['source']['path']); assert pin(source) == target['source']
dest = project / source.name; shutil.copyfile(source, dest)
plan['targets'] = [{**target, 'source': pin(dest), 'predecessor_source': target['source']}]
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
runner = ROOT / 'execute_bounded.py'; text = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(text)
runner.write_text(text, encoding='utf-8', newline='\n')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(PRIOR / 'plan.json'), pin(PRIOR / 'events.jsonl'),
    pin(PRIOR / 'runs/02-TorsionEulerInteger49/stdout.txt'), finished[0]['result']['stdout'], pin(T3 / 'plan.json'), target['source']] + originals + base
plan['kind'] = 'CLOSED_KERNEL_INTEGER_EULER_OWNED_IMPORT_SUCCESSOR'
plan['repairs'] = 'Original failed integer-certificate attempt missed the qualified Range/Spend transitive dependencies of CurveCardinalityWindow01. Fresh root includes the full four-module owned closure. All proof/definition source bytes unchanged; failed predecessor retained; no negative-control credit.'
plan['scope'] = 'One closed integer certificate module, six audits. No field/native/point/order/full Transfer claim.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'owned_closure': [Path(p['path']).name for p in base], 'repair': plan['repairs']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audit_pairs': 6}))
