"""Prepare only the generated torsion integer certificates, after the row bridge passes."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-concrete-no-sixteen-20261010-02'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
events = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines()]
done = [e for e in events if e['event'] == 'attempt_finished']
assert len(done) == len(plan['targets']) == 1 and done[0]['result']['status'] == 'passed'
originals = plan['owned_imports'] + done[0]['result']['objects']
odd = DIAG / 'transfer-cardinality-image-20261010-02'
odd_plan = json.loads((odd / 'plan.json').read_text())
odd_done = [json.loads(x) for x in (odd / 'events.jsonl').read_text().splitlines() if json.loads(x)['event'] == 'attempt_finished']
assert len(odd_done) == len(odd_plan['targets']) == 1 and odd_done[0]['result']['status'] == 'passed'
existing = {Path(r['path']).name: r for r in originals}
for r in odd_plan['owned_imports'] + odd_done[0]['result']['objects']:
    assert pin(r['path']) == r
    name = Path(r['path']).name
    if name in existing:
        assert existing[name]['bytes'] == r['bytes'] and existing[name]['sha256'] == r['sha256']
    else:
        originals.append(r); existing[name] = r
plan['pins'] += [pin(odd / 'plan.json'), pin(odd / 'events.jsonl'), odd_done[0]['result']['stdout']] + odd_plan['pins']

project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
base = []
for r in originals:
    assert pin(r['path']) == r
    dest = project / Path(r['path']).name; shutil.copyfile(r['path'], dest); base.append(pin(dest))
source = ROOT / 'handwritten/ConcreteCardinalityJoin01.lean'
dest = project / source.name; shutil.copyfile(source, dest)
text = source.read_text()
names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert names == re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) and len(names) == 2
runner = ROOT / 'execute_bounded.py'
body = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(body)
runner.write_text(body, encoding='utf-8', newline='\n')
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source),
    'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(ROOT / 'prepare_recipe.py'),
    pin(PRIOR / 'prepare_recipe.py'), pin(PRIOR / 'plan.json'),
    pin(PRIOR / 'events.jsonl'), done[0]['result']['stdout']] + originals + base
failed = DIAG / 'transfer-concrete-eight-witness-20261010-01'
history = [pin(failed / name) for name in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'prepare.py', 'prepare_recipe.py', 'handwritten/ConcreteEightTorsionWitness01.lean', 'runs/01-ConcreteEightTorsionWitness01/stdout.txt']]
plan['pins'] += history
plan['retained_failed_witness_history'] = history
failed_no16 = DIAG / 'transfer-concrete-no-sixteen-20261010-01'
failed_no16_history = [pin(failed_no16 / name) for name in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'prepare.py', 'prepare_recipe.py', 'handwritten/ConcreteNoSixteen01.lean', 'runs/01-ConcreteNoSixteen01/stdout.txt']]
plan['pins'] += failed_no16_history
plan['retained_failed_no16_history'] = failed_no16_history
plan['kind'] = 'ACTUAL_CARDINALITY_AND_GLOBAL_EXPONENT_WITH_EXPLICIT_BASE_ORDER'
plan['scope'] = 'Actual kernel8cardinality8, no16, oddimage and point bound discharge all curve-side obligations. Given an actual point with exact scalarModulus order, prove actual Nat.card curve.Point=8r and the global8r exponent. Exact runtime-base/order binding is explicitly retained; native/fullTransfer remain open.'
plan['repairs'] = 'New two-lemma handwritten actual cardinality join. No unqualified base-order premise is hidden, no conclusion asserted without it, and same complete external floor and finite guards.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'audits': len(names), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
