"""Closed kernel integer certificates; no ZMod, primality or point interpretation."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
FLOOR = DIAG / 'transfer-prerequisite-floor-20261010-06'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((FLOOR / 'plan.json').read_text())
prior = DIAG / 'transfer-torsion-euler-20261010-01/handwritten/TorsionEulerInteger49.lean'
text = prior.read_text().replace('ShielddSecurity.ModularPower', 'ShielddSecurity.NatModularPower01').replace('ModularPower.power', 'NatModularPower01.power')
text = text.replace('Their field interpretation requires NatModularPower01.power_sound and the actual', 'Their field interpretation requires a separately proved field soundness theorem and the actual')
dest = ROOT / 'handwritten/TorsionEulerInteger49.lean'
dest.write_text(text, encoding='utf-8', newline='\n')
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
qualified_task = DIAG / 'transfer-torsion-cardinality49-20261010-03'
events = [json.loads(x) for x in (qualified_task / 'events.jsonl').read_text().splitlines()]
window = next(e for e in events if e['event'] == 'attempt_finished' and e['module'] == 'CurveCardinalityWindow01')
assert window['result']['status'] == 'passed'
base = []
for p in window['result']['objects']:
    assert pin(p['path']) == p
    copied = project / Path(p['path']).name; shutil.copyfile(p['path'], copied); base.append(pin(copied))
targets = []
for name in ['NatModularPower01', 'TorsionEulerInteger49']:
    source = ROOT / 'handwritten' / (name + '.lean')
    copied = project / source.name; shutil.copyfile(source, copied)
    source_text = copied.read_text()
    names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', source_text, re.M)
    assert re.findall(r'^#check @([A-Za-z0-9_.]+)', source_text, re.M) == names
    targets.append({'module': name, 'source': pin(copied),
        'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', source_text, re.M), 'audit_names': names})
runner = ROOT / 'execute_bounded.py'
runner_text = (FLOOR / 'execute_bounded.py').read_text(); ast.parse(runner_text)
runner.write_text(runner_text, encoding='utf-8', newline='\n')
plan['targets'] = targets
plan['lean_path'][0] = str(ROOT / 'project')
plan['owned_imports'] = base
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(FLOOR / 'plan.json'), pin(prior),
    pin(qualified_task / 'plan.json'), pin(qualified_task / 'events.jsonl'), window['result']['stdout']]
plan['pins'] += window['result']['objects'] + base + [pin(ROOT / 'handwritten' / (t['module'] + '.lean')) for t in targets]
plan['kind'] = 'CLOSED_KERNEL_INTEGER_TORSION_EULER_CERTIFICATES'
plan['scope'] = 'Two modules, eight ordered audits. Exact Nat binary recurrence and three closed Euler residue checks. The recurrence has the same mathematical source as ModularPower but field soundness, concrete certified prime field, nonsquare interpretation, point order and curve cardinality are not established here.'
plan['repairs'] = 'Split pure integer recurrence from field interpretation so the closed finite certificate has only the qualified builtin Omega import. Source-only predecessor retained.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner),
    'guard': 'Exact complete-import executor and fixed finite limits retained. No field, native, global-cardinality or negative-control credit.'}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audit_pairs': sum(len(t['audit_names']) for t in targets)}))
