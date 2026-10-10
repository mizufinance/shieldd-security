"""Compare declaration-source bodies of shared cache variants; no proof credit."""
import hashlib
import json
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
old_review = DIAG / 'transfer-base-order-import-review-20261010-01/review.json'
old = json.loads(old_review.read_text())['owned']
new_plan_path = DIAG / 'transfer-concrete-cardinality-join-20261010-01/plan.json'
new = json.loads(new_plan_path.read_text())
def pin(path):
    path = Path(path)
    with path.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
def body(path):
    text = Path(path).read_text(encoding='utf-8-sig')
    lines = [line.rstrip() for line in text.splitlines() if line.strip()
        and not line.startswith('set_option pp.all true in')
        and not line.startswith('#check ') and not line.startswith('#print axioms ')]
    return '\n'.join(lines)
names = {Path(r['path']).stem: r for r in new['owned_imports']}
candidates = {}
for r in new['pins']:
    path = Path(r['path'])
    if path.suffix == '.lean' and path.is_file(): candidates.setdefault(path.stem, []).append(r)
qualified_numeric = []
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
results = []
for name, item in old.items():
    stem = name.split('.')[-1]
    if stem not in names: continue
    old_body = body(item['source']['path'])
    matching = []
    for candidate in candidates.get(stem, []):
        assert pin(candidate['path']) == candidate
        if body(candidate['path']) == old_body: matching.append(candidate)
    results.append({'module': name, 'old_source': item['source'], 'old_object': item['object'],
        'current_object': names[stem], 'same_declaration_source_body': bool(matching),
        'matching_current_sources': matching,
        'declaration_source_body_sha256': hashlib.sha256(old_body.encode()).hexdigest()})
review = {'old_closure': pin(old_review), 'current_plan': pin(new_plan_path),
    'parser': pin(Path(__file__)), 'modules': results, 'qualified_numeric_sources': qualified_numeric, 'retained_incomplete_comparison': pin(DIAG / 'transfer-base-order-shared-source-review-20261010-01/review.json'),
    'all_same_declaration_source_body': all(r['same_declaration_source_body'] for r in results),
    'scope': 'Source identity after removing only blank lines and full-type/axiom reporting directives. Same declaration-source body comparison is separate from object identity and does not replay old proofs or grant kernel credit.'}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2, sort_keys=True) + '\n')
print(json.dumps({'modules': len(results), 'all_same': review['all_same_declaration_source_body'],
    'mismatches': [r['module'] for r in results if not r['same_declaration_source_body']],
    'review': pin(ROOT / 'review.json')}))
