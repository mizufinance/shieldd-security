"""Finite first-eight semantic dependency batch, handwritten audit framing only."""
import ast
import hashlib
import importlib.util
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
spec = importlib.util.spec_from_file_location('guards', FLOOR / 'execute_bounded.py')
guards = importlib.util.module_from_spec(spec); spec.loader.exec_module(guards)
review_path = DIAG / 'transfer-semantic-subgroup48-20261010-01/dependency-review.json'
review = json.loads(review_path.read_text())
assert len(review['targets']) == 9
project = ROOT / 'project/ShielddSecurity'
project.mkdir(parents=True, exist_ok=False)
base = []; baseline_records = []
for task_name in ['transfer-prerequisite-floor-20261010-06', 'transfer-group-source47-20261010-05']:
    task = DIAG / task_name
    events = [json.loads(x) for x in (task / 'events.jsonl').read_text().splitlines()]
    finished = [e for e in events if e['event'] == 'attempt_finished']
    assert len(finished) == 8 and all(e['result']['status'] == 'passed' for e in finished)
    baseline_records += [pin(task / 'plan.json'), pin(task / 'events.jsonl')]
    for result in finished:
        baseline_records.append(result['result']['stdout'])
        for record in result['result']['objects']:
            assert pin(record['path']) == record
            dest = project / Path(record['path']).name
            shutil.copyfile(record['path'], dest)
            base.append(pin(dest)); baseline_records.append(record)
targets = []; changes = []
for item in review['targets'][:8]:
    source = Path(item['source']['path']); assert pin(source) == item['source']
    original = source.read_text()
    assert not item['generated']
    code = guards.code_only(original)
    namespace = re.findall(r'^namespace ([A-Za-z0-9_.]+)', code, re.M)
    assert namespace == [item['module']]
    names = re.findall(r'^(?:noncomputable\s+)?(?:def|abbrev|structure|inductive|theorem|lemma)\s+([A-Za-z0-9_.]+)', code, re.M)
    assert names and len(names) == len(set(names))
    audits = [namespace[0] + '.' + n for n in names]
    text = re.sub(r'(?m)^set_option pp.all true in\n#check[^\n]*\n', '', original)
    text = re.sub(r'(?m)^#(?:print axioms|check)[^\n]*\n', '', text)
    text = re.sub(r'set_option maxHeartbeats (\d+)', lambda m: 'set_option maxHeartbeats ' + str(min(int(m.group(1)), 300000)), text)
    if 'set_option maxRecDepth' not in text: text = text.replace('set_option maxHeartbeats', 'set_option maxRecDepth 4096\nset_option maxHeartbeats', 1)
    text += '\n' + '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in audits) + '\n'
    dest = project / source.name
    dest.write_text(text, encoding='utf-8', newline='\n')
    actual_imports, _ = guards.header(text)
    assert actual_imports == item['imports']
    targets.append({'module': source.stem, 'source': pin(dest), 'predecessor_source': item['source'],
        'imports': actual_imports, 'audit_names': audits})
    changes.append({'module': source.stem, 'source': item['source'], 'successor': pin(dest),
        'change': 'Handwritten source only: cap heartbeat at300000, rec4096, replace old audit commands by ordered full-type/axiom pairs for every explicit top-level named declaration. Proof/definition bodies and premises unchanged.', 'audit_pairs': len(audits)})
runner = ROOT / 'execute_bounded.py'
runner_text = (FLOOR / 'execute_bounded.py').read_text(); ast.parse(runner_text)
runner.write_text(runner_text, encoding='utf-8', newline='\n')
inventory = DIAG / 'transfer-external-floor-complete-20261010-03/external-floor.json'
assert json.loads(inventory.read_text())['admission_ready']
plan['external_floor'] = {**pin(inventory), 'admission_ready': True}
plan['targets'] = targets
plan['lean_path'][0] = str(ROOT / 'project')
plan['owned_imports'] = base
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(review_path), pin(FLOOR / 'plan.json'), pin(inventory)]
plan['pins'] += baseline_records + base + [t['predecessor_source'] for t in targets]
plan['kind'] = 'BOUNDED_HANDWRITTEN_SOURCE48_SEMANTIC_DEPENDENCIES'
plan['scope'] = 'First eight owned semantic/scalar dependencies; every explicit named declaration receives a full-type/axiom audit. Source48 bridge ninth is a separate successor after all required objects qualify. Native interpretation, concrete group/cardinality and full Transfer remain open.'
plan['repairs'] = changes
plan['artifact_policy'] = 'Only sixteen freshly qualified owned objects plus eight handwritten audit-framing sources; all new bytes counted. External objects read-only.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner),
    'targets': [t['module'] for t in targets], 'audits': sum(len(t['audit_names']) for t in targets),
    'changes': changes, 'guard': 'Exact strong corrected executor reused; all fixed host/memory/thread/finite budget/import/output/axiom guards retained.'}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'targets': [t['module'] for t in targets], 'audit_pairs': sum(len(t['audit_names']) for t in targets)}))
