"""Extend source-body comparison with exact passed numeric-tree sources and objects."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-base-order-shared-source-review-20261010-01'
recipe = (OLD / 'inspect.py').read_text()
needle = 'results = []'
addition = """qualified_numeric = []
for number in range(1, 6):
    task = DIAG / ('transfer-prime-tree-closed-20261010-%02d' % number)
    task_plan = json.loads((task / 'plan.json').read_text())
    events = [json.loads(x) for x in (task / 'events.jsonl').read_text().splitlines()]
    completed = [e for e in events if e['event'] == 'attempt_finished']
    assert len(completed) == len(task_plan['targets']) and all(e['result']['status'] == 'passed' for e in completed)
    for e in completed:
        target = next(t for t in task_plan['targets'] if t['module'] == e['module'])
        source = target['source']
        obj = e['result']['objects'][0]
        assert pin(source['path']) == source and pin(obj['path']) == obj
        assert obj['bytes'] == names[e['module']]['bytes'] and obj['sha256'] == names[e['module']]['sha256']
        candidates.setdefault(e['module'], []).append(source)
        qualified_numeric.append({'source': source, 'object': obj, 'plan': pin(task / 'plan.json'),
            'events': pin(task / 'events.jsonl'), 'stdout': e['result']['stdout']})
"""
assert recipe.count(needle) == 1
recipe = recipe.replace(needle, addition + needle)
recipe = recipe.replace("'parser': pin(Path(__file__)), 'modules': results,", "'parser': pin(Path(__file__)), 'modules': results, 'qualified_numeric_sources': qualified_numeric, 'retained_incomplete_comparison': pin(DIAG / 'transfer-base-order-shared-source-review-20261010-01/review.json'),")
(ROOT / 'inspect.py').write_text(recipe, encoding='utf-8', newline='\n')
print(ROOT / 'inspect.py')
