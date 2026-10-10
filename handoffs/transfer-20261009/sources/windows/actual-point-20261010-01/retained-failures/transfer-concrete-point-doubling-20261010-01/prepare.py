"""One finite actual Point-doubling replay after its exact Point join passes."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
parser = argparse.ArgumentParser()
parser.add_argument('--point-task', required=True)
args = parser.parse_args()
assert re.fullmatch(r'transfer-concrete-point-torsion-20261010-[0-9]{2}', args.point_task)
PRIOR = DIAG / args.point_task

def pin(p):
    p = Path(p)
    with p.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}

plan = json.loads((PRIOR / 'plan.json').read_text())
originals = {}; receipts = []
for task, selected in [(PRIOR, 'ConcretePointTorsion01'),
                       (DIAG / 'transfer-torsion-cardinality49-20261010-03', 'WeierstrassDoublingSquare01')]:
    previous = json.loads((task / 'plan.json').read_text())
    events = [json.loads(x) for x in (task / 'events.jsonl').read_text().splitlines()]
    done = [e for e in events if e['event'] == 'attempt_finished']
    assert len(done) == len(previous['targets']) and all(e['result']['status'] == 'passed' for e in done)
    result = next(e['result'] for e in done if e['module'] == selected)
    for r in previous['owned_imports'] + result['objects']:
        assert pin(r['path']) == r
        key = Path(r['path']).name
        if key in originals:
            assert originals[key]['sha256'] == r['sha256'], key
        originals[key] = r
    receipts += [pin(task / 'plan.json'), pin(task / 'events.jsonl'), result['stdout']]
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
base = []
for key, r in originals.items():
    dest = project / key; shutil.copyfile(r['path'], dest); base.append(pin(dest))
source = ROOT / 'handwritten/ConcretePointDoublingSquare01.lean'
dest = project / source.name; shutil.copyfile(source, dest)
text = source.read_text(); names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert names == re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) and len(names) == 6
runner = ROOT / 'execute_bounded.py'
body = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(body)
runner.write_text(body, encoding='utf-8', newline='\n')
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source), 'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source)] + list(originals.values()) + base + receipts
plan['kind'] = 'ACTUAL_POINT_DOUBLING_SQUARE_AND_TWO_NONSQUARE_NO_HALVES'
plan['scope'] = 'Actual regular doubling branch of the concrete Mathlib curve Point group has square output X. Points with either closed Euler-nonsquare X firstX or secondX have no half, for any Y satisfying the curve equation. Complete order8 torsion enumeration/no16, base order, final cardinality, native and full Transfer remain open.'
plan['repairs'] = 'New handwritten bridge from the actual Point doubling/slope to the existing symbolic tangent square proof; exact complete owned import closure and unchanged finite guards.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'audits': len(names), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
