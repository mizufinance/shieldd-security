"""Copy one complete qualified owned package under the reviewed packaging cap.

This is identity admission only. No kernel, runtime, negative-control or
certification credit is granted by copying. Every new file is charged here.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CAP = 128 * 1024**2
STAGES = [('transfer-concrete-standard-model-20261010-03', 1),
          ('transfer-concrete-standard-model-20261010-08', 2),
          ('transfer-concrete-standard-model-20261010-10', 1),
          ('transfer-concrete-standard-model-20261010-13', 3),
          ('transfer-concrete-standard-model-20261010-18', 1),
          ('transfer-concrete-standard-model-20261010-20', 5),
          ('transfer-concrete-standard-model-20261010-21', 1),
          ('transfer-concrete-standard-model-20261010-22', 3),
          ('transfer-concrete-cofactor-model-20261010-02', 1),
          ('transfer-sdk-extended-model-20261010-03', 1),
          ('transfer-sdk-concrete-model-20261010-01', 1),
          ('transfer-sdk-multiply-model-20261010-03', 1),
          ('transfer-concrete-admission-model-20261010-01', 1),
          ('transfer-sdk-admission-model-20261010-05', 1),
          ('transfer-sdk-spend-auth-certificates-20261010-01', 1)]
def pin(path):
    path = Path(path)
    with path.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
def verify(records):
    for r in records:
        assert pin(r['path']) == r

prior = DIAG / 'transfer-concrete-standard-model-closure-review-20261010-02/review.json'
review = json.loads(prior.read_text())
assert review['existing_count'] == 384 and review['kernel_credit'] == 0
assert not review['unused_pool']
selected = {r['module']: r for r in review['selected']}
inputs = [pin(prior)] + review['input_records'] + review['source_pins']
for task, count in STAGES:
    task = DIAG / task
    plan = json.loads((task / 'plan.json').read_text())
    events = [json.loads(line) for line in (task / 'events.jsonl').read_text().splitlines()]
    passes = [e for e in events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']
    assert len(passes) == count
    if count in (3, 4, 5):
        assert events[-1]['result']['status'] == 'passed'
    for e in passes:
        target = next(t for t in plan['targets'] if t['module'] == e['module'])
        result = e['result']
        assert len(result['objects']) == 1
        assert len(result['audits']) == len(target['audit_names'])
        assert all(set(a['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in result['audits'].values())
        assert e['module'] not in selected
        selected[e['module']] = {'module': e['module'], 'object': result['objects'][0],
                                  'source': target['source'], 'receipt': result,
                                  'qualified_plan': pin(task / 'plan.json')}
    inputs += [pin(task / name) for name in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'prepare.py', 'review.json']]
assert len(selected) == 408
verify(inputs)
verify([r[key] for r in selected.values() for key in ['object', 'source']])
assert shutil.disk_usage(ROOT).free > 2 * 1024**3
assert sum(r['object']['bytes'] for r in selected.values()) + 8 * 1024**2 < CAP
package = ROOT / 'modules/ShielddSecurity'
package.mkdir(parents=True, exist_ok=False)
copied = []
for name, r in sorted(selected.items()):
    target = package / (name + '.olean')
    assert not target.exists()
    shutil.copyfile(r['object']['path'], target)
    copy = pin(target)
    assert (copy['bytes'], copy['sha256']) == (r['object']['bytes'], r['object']['sha256'])
    copied.append({**r, 'copy': copy})
    assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < CAP
assert {str(p) for p in package.iterdir()} == {r['copy']['path'] for r in copied}
verify(inputs)
verify([r[key] for r in copied for key in ['object', 'source', 'copy']])
composition = {'admission_ready': True, 'kernel_credit': 0, 'selected': copied,
               'input_records': inputs, 'prepare_recipe': pin(Path(__file__)),
               'objects': len(copied), 'charged_new_object_bytes': sum(r['copy']['bytes'] for r in copied),
               'artifact_cap_bytes': CAP, 'metadata_cap_bytes': 16 * 1024**2,
               'superseded_unrun_partition_recipe': pin(DIAG / 'transfer-concrete-cofactor-floor-recipe-20261010-01/prepare.py'),
               'scope': 'Complete immutable first owned package root:384 retained qualified cardinality/base objects plus24 newly qualified addition/model/native-contract/cofactor/SDK arithmetic, multiplication, admission and SpendAuth certificate objects. Every copied object is fully charged in this job. Copy identity is not semantic correspondence or new proof credit.'}
pending = ROOT / 'composition-review.json.pending'
pending.write_text(json.dumps(composition, indent=2, sort_keys=True) + '\n')
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < CAP
assert pending.stat().st_size < 16 * 1024**2
os.replace(pending, ROOT / 'composition-review.json')
print(json.dumps({'review': pin(ROOT / 'composition-review.json'), 'objects': len(copied),
                  'charged_new_object_bytes': composition['charged_new_object_bytes'],
                  'actual_task_bytes': sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()),
                  'kernel_credit': 0}))
