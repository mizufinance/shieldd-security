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
body = (PRIOR / 'execute_bounded.py').read_text()
old_usage = """    files = [p for p in ROOT.rglob('*') if p.is_file()]
    total = sum(p.stat().st_size for p in files)
    metadata = sum(p.stat().st_size for p in files if p.suffix in ('.json', '.jsonl', '.txt'))"""
new_usage = """    files = [p for p in ROOT.rglob('*') if p.is_file()]
    sizes = [(p, live_artifact_size(p)) for p in files]
    total = sum(size for _, size in sizes)
    metadata = sum(size for p, size in sizes if p.suffix in ('.json', '.jsonl', '.txt'))"""
assert body.count(old_usage) == 1
body = body.replace(old_usage, new_usage)
old_artifact = "artifact.stat().st_size > OBJECT_CAP"
assert body.count(old_artifact) == 1
body = body.replace(old_artifact, "live_artifact_size(artifact) > OBJECT_CAP")
helper = """def live_artifact_size(path):
    try:
        return path.stat().st_size
    except FileNotFoundError:
        # Lean atomically renames named export temporaries. Accept only a
        # vanished temporary belonging to this plan's target output folder.
        # Every extant temporary/final file is counted again on the next poll,
        # and final output/usage checks run after Lean and its reader exit.
        if (path.parent == ROOT / 'project' / 'ShielddSecurity'
                and '.tmp.' in path.name
                and any(path.name.startswith(t['module'] + '.') for t in PLAN['targets'])):
            return 0
        raise


"""
assert body.count('def usage():') == 1
body = body.replace('def usage():', helper + 'def usage():')
ast.parse(body)
runner.write_text(body, encoding='utf-8', newline='\n')
floor = DIAG / 'transfer-external-floor-complete-20261010-10/external-floor.json'
assert json.loads(floor.read_text())['admission_ready']
plan['external_floor'] = {**pin(floor), 'admission_ready': True}
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source), 'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
plan['owned_imports'] = base
plan['lean_path'][0] = str(ROOT / 'project')
plan['lean_path'][1] = str(DIAG / 'transfer-point-package-composed-20261010-01/modules')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(floor), pin(DIAG / 'transfer-point-package-composed-20261010-01/composition-review.json')] + list(originals.values()) + base + receipts
failed = DIAG / 'transfer-concrete-point-torsion-20261010-01'
history = [failed / 'plan.json', failed / 'events.jsonl', failed / 'prepare.py',
    failed / 'handwritten/ConcretePointTorsion01.lean',
    failed / 'runs/01-ConcretePointTorsion01/stdout.txt']
plan['pins'] += [pin(p) for p in history] + [pin(DIAG / 'transfer-concrete-point-repair-recipe-20261010-01/prepare.py')]
second_failed = DIAG / 'transfer-concrete-point-torsion-20261010-02'
second_history = [second_failed / 'plan.json', second_failed / 'events.jsonl',
    second_failed / 'prepare.py', second_failed / 'execute_bounded.py',
    second_failed / 'handwritten/ConcretePointTorsion01.lean',
    second_failed / 'runs/01-ConcretePointTorsion01/stdout.txt']
plan['pins'] += [pin(p) for p in second_history] + [pin(DIAG / 'transfer-concrete-point-race-recipe-20261010-01/prepare.py')]
plan['retained_failed_history'] = [pin(p) for p in history + second_history]
plan['kind'] = 'ACTUAL_CONCRETE_POINT_BOUND_AND_TWO_TORSION_CLASSIFICATION' 
plan['scope'] = 'Actual prime field, nonsingular full Mathlib Point group for coefficients A40962/B-40964. Discriminant nonzero, finite full point set, at most2p+1 points, two-torsion only zero/origin, origin has exact order2, eight-kernel at most8. Eight-point lower bound/exhaustiveness, no16, base order, final cardinality, native and full Transfer remain open.'
plan['repairs'] = 'Unchanged handwritten Point02 proof. Preserve failed01/02 as zero-credit. Narrow executor fix: tolerate only a disappeared named target .tmp. export during live size sampling; extant/final files remain counted, immutable inputs remain strict, all caps and final audits unchanged.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'audits': len(names), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
