"""Fresh corrected-import symbolic rebuild plus a new two-torsion algebra module."""
import ast
import hashlib
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
events = [json.loads(line) for line in (FLOOR / 'events.jsonl').read_text().splitlines()]
finished = [e for e in events if e['event'] == 'attempt_finished']
assert len(finished) == 8 and all(e['result']['status'] == 'passed' for e in finished)
project = ROOT / 'project' / 'ShielddSecurity'
project.mkdir(parents=True, exist_ok=False)
old_base = [p for e in finished if e['module'] in ('SpendGateInputs', 'Range') for p in e['result']['objects']]
assert len(old_base) == 2
base = []
for p in old_base:
    assert pin(p['path']) == p
    dest = project / Path(p['path']).name
    shutil.copyfile(p['path'], dest)
    base.append(pin(dest))
source_paths = [DIAG / 'transfer-torsion-cardinality49-20261010-02/project/ShielddSecurity' / (n + '.lean')
    for n in ['CurveCardinalityWindow01', 'WeierstrassDoublingSquare01']]
source_paths += [DIAG / 'transfer-torsion-algebra-20261010-01/handwritten/WeierstrassTwoTorsionAlgebra01.lean']
targets = []
for source in source_paths:
    dest = project / source.name
    shutil.copyfile(source, dest)
    text = dest.read_text()
    names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
    assert re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) == names
    targets.append({'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source),
        'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names})
runner = ROOT / 'execute_bounded.py'
text = (FLOOR / 'execute_bounded.py').read_text()
ast.parse(text)
runner.write_text(text, encoding='utf-8', newline='\n')
plan['targets'] = targets
plan['lean_path'][0] = str(ROOT / 'project')
plan['owned_imports'] = base
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(FLOOR / 'plan.json'), pin(FLOOR / 'events.jsonl')]
plan['pins'] += old_base + base + [e['result']['stdout'] for e in finished if e['module'] in ('SpendGateInputs', 'Range')] + [t['predecessor_source'] for t in targets]
plan['kind'] = 'FRESH_COMPLETE_IMPORT_TORSION_SYMBOLIC_PROOFS'
plan['scope'] = 'Three symbolic handwritten modules with10 declaration audits. Exact integer bound/reduction, tangent square coordinate, discriminant scaling, zero-Y X classification and fibre alternatives. Concrete curve/group/finite certificates remain separate and open.'
plan['predecessor'] = {'fresh_floor_events': pin(FLOOR / 'events.jsonl'),
    'old_symbolic_events_observations_only': pin(DIAG / 'transfer-torsion-cardinality49-20261010-02/events.jsonl')}
plan['repairs'] = {'guard': 'Corrected complete import qualification inherited; affected old objects excluded.',
    'source': 'Two exact calibrated symbolic sources plus one new small handwritten algebra source.'}
plan['artifact_policy'] = 'Only two fresh qualified floor objects, three sources and new outputs/metadata copied and counted.'
plan['invocation'] = 'Queue after current Group rebuild; pinned Python -B and exact reviewed plan SHA. No concurrent heavy job.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
review = {'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'targets': [t['module'] for t in targets],
    'audit_pairs': sum(len(t['audit_names']) for t in targets), 'guard_review': 'Corrected import/header validation and all finite safety/audit limits retained.'}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review, indent=2))
