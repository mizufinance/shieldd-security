"""Fresh Scalar linter repair with successful semantic prefix retained."""
import ast
import hashlib
import json
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-semantic-source48-20261010-04'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
events = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines()]
done = [e for e in events if e['event'] == 'attempt_finished']
assert len(done) == 3 and all(e['result']['status'] == 'passed' for e in done[:2])
assert done[-1]['module'] == 'Scalar' and done[-1]['result']['status'] == 'failed'
stdout = PRIOR / 'runs/03-Scalar/stdout.txt'
assert stdout.read_text().count('warning:') == 3 and 'error:' not in stdout.read_text()
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
originals = plan['owned_imports'] + [p for e in done[:2] for p in e['result']['objects']]
base = []
for p in originals:
    assert pin(p['path']) == p
    dest = project / Path(p['path']).name; shutil.copyfile(p['path'], dest); base.append(pin(dest))
targets = []
for target in plan['targets'][2:]:
    p = target['source']; assert pin(p['path']) == p
    text = Path(p['path']).read_text()
    if target['module'] == 'Scalar':
        assert text.count('simp [comparisonStep] <;> omega') == 2
        assert text.count('    simpa using nonzeroRow') == 1
        text = text.replace('simp [comparisonStep] <;> omega', 'simp [comparisonStep]; omega')
        text = text.replace('    simpa using nonzeroRow', '    simp at nonzeroRow')
    dest = project / Path(p['path']).name; dest.write_text(text, encoding='utf-8', newline='\n')
    targets.append({**target, 'source': pin(dest), 'predecessor_source': p})
runner = ROOT / 'execute_bounded.py'; text = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(text)
runner.write_text(text, encoding='utf-8', newline='\n')
plan['targets'] = targets; plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(PRIOR / 'plan.json'), pin(PRIOR / 'events.jsonl'), pin(stdout)] + originals + base + [e['result']['stdout'] for e in done[:2]] + [t['predecessor_source'] for t in targets]
plan['predecessor'] = {'plan': pin(PRIOR / 'plan.json'), 'events': pin(PRIOR / 'events.jsonl'), 'failure': done[-1]}
plan['kind'] = 'BOUNDED_HANDWRITTEN_SOURCE48_SCALAR_LINT_SUCCESSOR'
plan['repairs'] = 'Scalar only: two single-goal <;> omega sequences become ; omega, and simpa using an impossible nonzeroRow becomes simp at nonzeroRow. Theorem signatures and hypotheses unchanged. Successful semantic prefix reused; all failed predecessors retained, zero negative-control credit.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'repair': plan['repairs']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'targets': [t['module'] for t in targets], 'audit_pairs': sum(len(t['audit_names']) for t in targets)}))
