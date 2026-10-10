"""Fresh successor fixing comment placement; proof and definition bodies unchanged."""
import ast
import hashlib
import json
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-semantic-source48-20261010-03'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
events = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines()]
done = [e for e in events if e['event'] == 'attempt_finished']
assert len(done) == 1 and done[0]['module'] == 'TransferSem' and done[0]['result']['status'] == 'failed'
stdout = PRIOR / 'runs/01-TransferSem/stdout.txt'
assert "unexpected token 'set_option'" in stdout.read_text()
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
base = []
for p in plan['owned_imports']:
    assert pin(p['path']) == p
    dest = project / Path(p['path']).name; shutil.copyfile(p['path'], dest); base.append(pin(dest))
targets = []
for target in plan['targets']:
    p = target['source']; assert pin(p['path']) == p
    text = Path(p['path']).read_text()
    if target['module'] == 'TransferSem':
        old = '/-- The established public API deliberately repeats its module namespace. -/'
        assert text.count(old) == 1
        text = text.replace(old, '-- The established public API deliberately repeats its module namespace.')
    dest = project / Path(p['path']).name; dest.write_text(text, encoding='utf-8', newline='\n')
    targets.append({**target, 'source': pin(dest), 'predecessor_source': p})
runner = ROOT / 'execute_bounded.py'
text = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(text)
runner.write_text(text, encoding='utf-8', newline='\n')
plan['targets'] = targets; plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(PRIOR / 'plan.json'), pin(PRIOR / 'events.jsonl'), pin(stdout)] + base + [t['predecessor_source'] for t in targets]
plan['predecessor'] = {'plan': pin(PRIOR / 'plan.json'), 'events': pin(PRIOR / 'events.jsonl'), 'failure': done[0]}
plan['kind'] = 'BOUNDED_HANDWRITTEN_SOURCE48_COMMENT_PLACEMENT_SUCCESSOR'
plan['repairs'] = 'A doc comment before the scoped set_option command was rejected by Lean syntax. Replace only that new doc comment by an ordinary line comment. Scoped duplicate-namespace lint exception retained, all proof/definition bodies and budgets unchanged. Both failed predecessors retained; zero negative-control credit.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'repair': plan['repairs']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audit_pairs': sum(len(t['audit_names']) for t in targets)}))
