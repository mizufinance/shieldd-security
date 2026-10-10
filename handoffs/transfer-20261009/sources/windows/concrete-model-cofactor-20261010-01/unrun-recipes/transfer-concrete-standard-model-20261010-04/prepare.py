"""Prepare a finite named addition-model batch from maintained handwritten sources."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-concrete-standard-model-20261010-03'
PUB = Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity')
MODULES = ['EdwardsExceptionalClassification01', 'ConcretePoleAddition01', 'EdwardsSecantPolynomials01', 'EdwardsSecantRational01', 'ConcreteSecantAddition01']

def pin(path):
    path = Path(path)
    with path.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}

plan = json.loads((PRIOR / 'plan.json').read_text())
done = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines()
        if json.loads(x)['event'] == 'attempt_finished']
assert len(done) == len(plan['targets']) and all(e['result']['status'] == 'passed' for e in done)
pool = json.loads(Path(plan['owned_import_pool']['path']).read_text())
selected = {Path(r['copy']['path']).name: r['copy'] for r in pool['selected']}
originals = plan['owned_imports'] + [r for e in done for r in e['result']['objects']]
project = ROOT / 'project/ShielddSecurity'
project.mkdir(parents=True, exist_ok=False)
handwritten = ROOT / 'handwritten'
handwritten.mkdir(exist_ok=False)
owned = []
records = []
for record in originals:
    assert pin(record['path']) == record
    name = Path(record['path']).name
    if name in selected:
        assert record == selected[name]
        owned.append(record)
    else:
        dest = project / name
        shutil.copyfile(record['path'], dest)
        owned.append(pin(dest))
        records.extend([record, pin(dest)])

targets = []
for module in MODULES:
    original = PUB / (module + '.lean')
    text = original.read_text()
    if module == 'EdwardsTorsionAlgebra01':
        needle = '  field_simp [nonzeroX] <;> ring'
        assert text.count(needle) == 1
        text = text.replace(needle, '  field_simp [nonzeroX]')
    assert not re.search(r'\b(sorry|admit|axiom)\b', re.sub(r'(?s)/\-.*?\-/', '', text))
    assert len(re.findall(r'^namespace ', text, re.M)) == 1
    namespace = re.findall(r'^namespace (\S+)', text, re.M)[0]
    names = re.findall(r'^(?:noncomputable )?(?:theorem|lemma|def) ([A-Za-z0-9_]+)', text, re.M)
    assert names
    assert all(int(x) <= 300000 for x in re.findall(r'set_option maxHeartbeats (\d+)', text))
    assert all(int(x) <= 4096 for x in re.findall(r'set_option maxRecDepth (\d+)', text))
    # Reporting commands alone change: every declaration/proof body is retained.
    body = '\n'.join(line for line in text.splitlines() if not (
        line.strip() == 'set_option pp.all true in' or
        line.lstrip().startswith('#check ') or line.lstrip().startswith('#print axioms '))) + '\n'
    qualified = [namespace + '.' + name for name in names]
    for name in qualified:
        body += '\nset_option pp.all true in\n#check @' + name + '\n#print axioms ' + name + '\n'
    source = handwritten / original.name
    source.write_text(body, encoding='utf-8', newline='\n')
    dest = project / original.name
    shutil.copyfile(source, dest)
    targets.append({'module': module, 'source': pin(dest), 'predecessor_source': pin(source),
                    'imports': re.findall(r'^import\s+(\S+)', body, re.M), 'audit_names': qualified})
    records.extend([pin(original), pin(source), pin(dest)])

runner_text = (PRIOR / 'execute_bounded.py').read_text()
assert 'Unexpected initial owned object location' in runner_text
ast.parse(runner_text)
runner = ROOT / 'execute_bounded.py'
runner.write_text(runner_text, encoding='utf-8', newline='\n')
plan['targets'] = targets
plan['owned_imports'] = owned
plan['lean_path'][1] = str(ROOT / 'project')
records.extend([pin(runner), pin(Path(__file__)), pin(PRIOR / 'plan.json'),
                pin(PRIOR / 'events.jsonl'), pin(PRIOR / 'execute_bounded.py')])
records.extend(e['result']['stdout'] for e in done)
failed = DIAG / 'transfer-concrete-standard-model-20261010-01'
records += [pin(failed / name) for name in ['prepare.py', 'plan.json', 'review.json',
    'events.jsonl', 'execute_bounded.py', 'runs/01-EdwardsTorsionAlgebra01/stdout.txt']]
records += [pin(p) for p in (failed / 'handwritten').glob('*.lean')]
records += [pin(ROOT / 'prepare_recipe.py')]
plan['pins'] += records
unique = {}
for record in plan['pins']:
    assert record['path'] not in unique or unique[record['path']] == record
    unique[record['path']] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'FINITE_CONCRETE_STANDARD_MODEL_ADDITION_BATCH'
plan['scope'] = 'Replay five exceptional/secant addition modules after the corrected first batch. All retained failed receipts remain zero credit. Full types and standard axioms; native/full Transfer open.'
plan['repairs'] = 'Only own_cache initial-keyset generalization: exact immutable pool subset plus explicit completed predecessor output copies inside own project. Every extra copied byte charged in this task; accepted cache keyset, pins, external floor, resource caps and output reservation unchanged.'
(ROOT / 'plan.json').write_text(json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n')
review = {'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'targets': [t['module'] for t in targets],
          'audit_count': sum(len(t['audit_names']) for t in targets), 'scope': plan['scope'],
          'runner_change': plan['repairs']}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
