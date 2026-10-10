"""Preserve first batch, reuse qualified Core, and scope the intentional API-name lint."""
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-semantic-source48-20261010-02'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
events = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines()]
done = [e for e in events if e['event'] == 'attempt_finished']
assert len(done) == 2 and done[0]['module'] == 'TransferCore' and done[0]['result']['status'] == 'passed'
assert done[1]['module'] == 'TransferSem' and done[1]['result']['status'] == 'failed'
output = PRIOR / 'runs/02-TransferSem/stdout.txt'
assert output.read_text().count('warning:') == 1 and 'namespace \'TransferSem\' is duplicated' in output.read_text()
assert 'error:' not in output.read_text()
spec = importlib.util.spec_from_file_location('guards', PRIOR / 'execute_bounded.py')
guards = importlib.util.module_from_spec(spec); spec.loader.exec_module(guards)
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
base = []
for p in plan['owned_imports'] + done[0]['result']['objects']:
    assert pin(p['path']) == p
    dest = project / Path(p['path']).name; shutil.copyfile(p['path'], dest); base.append(pin(dest))
targets = []
for old in plan['targets'][1:]:
    source = Path(old['source']['path']); assert pin(source) == old['source']
    text = source.read_text()
    if old['module'] == 'TransferSem':
        needle = 'def TransferSem (c : Crypto)'
        assert text.count(needle) == 1
        text = text.replace(needle, '/-- The established public API deliberately repeats its module namespace. -/\nset_option linter.dupNamespace false in\n' + needle)
    dest = project / source.name; dest.write_text(text, encoding='utf-8', newline='\n')
    targets.append({**old, 'source': pin(dest), 'predecessor_source': old['source']})
bridge = DIAG / 'transfer-semantic-subgroup48-20261010-01/inputs/ShielddSecurity/TransferSemanticSubgroup48.lean'
original = bridge.read_text()
code = guards.code_only(original)
namespace = re.findall(r'^namespace ([A-Za-z0-9_.]+)', code, re.M)
assert namespace == ['ShielddSecurity.TransferSemanticSubgroup48']
names = re.findall(r'^(?:noncomputable\s+)?(?:def|abbrev|structure|inductive|theorem|lemma)\s+([A-Za-z0-9_.]+)', code, re.M)
audits = [namespace[0] + '.' + n for n in names]; assert len(audits) == 11
text = re.sub(r'(?m)^set_option pp.all true in\n#check[^\n]*\n', '', original)
text = re.sub(r'(?m)^#(?:print axioms|check)[^\n]*\n', '', text)
text += '\n' + '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in audits) + '\n'
dest = project / bridge.name; dest.write_text(text, encoding='utf-8', newline='\n')
imports, _ = guards.header(text)
targets.append({'module': bridge.stem, 'source': pin(dest), 'predecessor_source': pin(bridge), 'imports': imports, 'audit_names': audits})
runner = ROOT / 'execute_bounded.py'
runner_text = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(runner_text)
runner.write_text(runner_text, encoding='utf-8', newline='\n')
plan['targets'] = targets; plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(PRIOR / 'plan.json'), pin(PRIOR / 'events.jsonl'),
    pin(output), done[0]['result']['stdout']] + base + done[0]['result']['objects'] + [t['predecessor_source'] for t in targets]
plan['predecessor'] = {'plan': pin(PRIOR / 'plan.json'), 'events': pin(PRIOR / 'events.jsonl'), 'failure': done[1]}
plan['kind'] = 'BOUNDED_HANDWRITTEN_SEMANTIC_SOURCE48_LINT_SUCCESSOR'
plan['repairs'] = 'Only a declaration-scoped linter.dupNamespace exception for the established TransferSem.TransferSem public API name; all definition/proof bodies, premises and resource limits unchanged. Add ninth bridge after the seven remaining dependency targets. Failed predecessor retained; zero negative-control credit.'
plan['scope'] = 'Eight targets including semantic subgroup interpretation bridge. Prior TransferCore qualified; runtime predicate correspondence, concrete group/cardinality and full Transfer remain open.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner),
    'repair': plan['repairs'], 'targets': [t['module'] for t in targets], 'audits': sum(len(t['audit_names']) for t in targets)}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'targets': [t['module'] for t in targets], 'audit_pairs': sum(len(t['audit_names']) for t in targets)}))
