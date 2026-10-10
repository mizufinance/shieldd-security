"""Prepare only the generated torsion integer certificates, after the row bridge passes."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-concrete-point-coordinate-20261010-01'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
events = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines()]
done = [e for e in events if e['event'] == 'attempt_finished']
assert len(done) == len(plan['targets']) == 1 and done[0]['result']['status'] == 'passed'
originals = plan['owned_imports'] + done[0]['result']['objects']
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
base = []
for r in originals:
    assert pin(r['path']) == r
    dest = project / Path(r['path']).name; shutil.copyfile(r['path'], dest); base.append(pin(dest))
source = ROOT / 'generated/ConcreteEightTorsionData01.lean'
review = json.loads((ROOT / 'generation-review.json').read_text())
assert review['source'] == pin(source) and review['generator'] == pin(ROOT / 'generate.py')
assert review['input'] == pin(review['input']['path']) and review['kernel_credit'] == 0
dest = project / source.name; shutil.copyfile(source, dest)
text = source.read_text()
names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert names == re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) and len(names) == 15
runner = ROOT / 'execute_bounded.py'
body = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(body)
runner.write_text(body, encoding='utf-8', newline='\n')
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source),
    'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(ROOT / 'generate.py'),
    pin(ROOT / 'generation-review.json'), review['input'], pin(PRIOR / 'plan.json'),
    pin(PRIOR / 'events.jsonl'), done[0]['result']['stdout']] + originals + base
plan['kind'] = 'KERNEL_CHECKED_ACTUAL_THREE_TORSION_COORDINATE_CERTIFICATES'
plan['scope'] = 'Exact field equations for three finite candidates and integer-backed rows for double1=point2, double2=origin, and point1+point2=point3. Coordinates are in the actual certified field. Exact orders/eight-point enumeration/no16/cardinality, native and full Transfer remain open.'
plan['repairs'] = 'Generated finite integer congruences from pinned DATA; kernel decide checks certificate arithmetic, followed by certified-field cast and actual coordinate-row interfaces. No generated source hand edits and same finite replay guards.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'audits': len(names), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
