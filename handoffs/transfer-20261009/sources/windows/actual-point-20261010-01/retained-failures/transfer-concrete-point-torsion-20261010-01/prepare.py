"""Connect only passed actual-field and generic-bound objects to actual Point."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-torsion-certified-field-20261010-01'

def pin(p):
    p = Path(p)
    with p.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}

plan = json.loads((PRIOR / 'plan.json').read_text())
originals = {}; receipts = []
for task in [PRIOR, DIAG / 'transfer-affine-fibre-bound-20261010-03', DIAG / 'transfer-doubling-kernel-bound-20261010-04']:
    previous = json.loads((task / 'plan.json').read_text())
    events = [json.loads(x) for x in (task / 'events.jsonl').read_text().splitlines()]
    done = [e for e in events if e['event'] == 'attempt_finished']
    assert len(done) == len(previous['targets']) and all(e['result']['status'] == 'passed' for e in done)
    for r in previous['owned_imports'] + [r for e in done for r in e['result']['objects']]:
        assert pin(r['path']) == r
        key = Path(r['path']).name
        if key in originals:
            assert originals[key]['sha256'] == r['sha256'], key
        originals[key] = r
    receipts += [pin(task / 'plan.json'), pin(task / 'events.jsonl')] + [e['result']['stdout'] for e in done]
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
base = []
for key, r in originals.items():
    dest = project / key; shutil.copyfile(r['path'], dest); base.append(pin(dest))
source = ROOT / 'handwritten/ConcretePointTorsion01.lean'
dest = project / source.name; shutil.copyfile(source, dest)
text = source.read_text(); names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert names == re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) and len(names) == 17
runner = ROOT / 'execute_bounded.py'
body = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(body)
runner.write_text(body, encoding='utf-8', newline='\n')
floor = DIAG / 'transfer-external-floor-complete-20261010-10/external-floor.json'
assert json.loads(floor.read_text())['admission_ready']
plan['external_floor'] = {**pin(floor), 'admission_ready': True}
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source), 'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
plan['owned_imports'] = base
plan['lean_path'][0] = str(ROOT / 'project')
plan['lean_path'][1] = str(DIAG / 'transfer-point-package-composed-20261010-01/modules')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(floor), pin(DIAG / 'transfer-point-package-composed-20261010-01/composition-review.json')] + list(originals.values()) + base + receipts
plan['kind'] = 'ACTUAL_CONCRETE_POINT_BOUND_AND_TWO_TORSION_CLASSIFICATION'
plan['scope'] = 'Actual prime field, nonsingular full Mathlib Point group for coefficients A40962/B-40964. Discriminant nonzero, finite full point set, at most2p+1 points, two-torsion only zero/origin, origin has exact order2, eight-kernel at most8. Eight-point lower bound/exhaustiveness, no16, base order, final cardinality, native and full Transfer remain open.'
plan['repairs'] = 'New handwritten actual Point join with complete exact owned import closure, completed official-cache first package composition and unchanged finite executor limits.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'audits': len(names), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
