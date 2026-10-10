"""Prepare only the generated torsion integer certificates, after the row bridge passes."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-concrete-eight-data-20261010-01'
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
source = ROOT / 'handwritten/ConcreteEightTorsionWitness01.lean'
dest = project / source.name; shutil.copyfile(source, dest)
text = source.read_text()
names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert names == re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) and len(names) == 11
runner = ROOT / 'execute_bounded.py'
body = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(body)
runner.write_text(body, encoding='utf-8', newline='\n')
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source),
    'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(ROOT / 'prepare_recipe.py'),
    pin(PRIOR / 'generate.py'), pin(PRIOR / 'generation-review.json'), pin(PRIOR / 'plan.json'),
    pin(PRIOR / 'events.jsonl'), done[0]['result']['stdout']] + originals + base
failed = DIAG / 'transfer-concrete-eight-witness-20261010-01'
history = [pin(failed / name) for name in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'prepare.py', 'prepare_recipe.py', 'handwritten/ConcreteEightTorsionWitness01.lean', 'runs/01-ConcreteEightTorsionWitness01/stdout.txt']]
plan['pins'] += history
plan['retained_failed_witness_history'] = history
plan['kind'] = 'ACTUAL_ORDER_EIGHT_WITNESS_AND_EXHAUSTIVE_EIGHT_KERNEL'
plan['scope'] = 'Actual coordinate rows imply point1 double=point2, point2 double=origin, point1 triple=point3. Point1 has exact order8. Fin8 multiples inject/surject onto actual kernel8, so its cardinality is exactly8 and every point killed by8 is enumerated. No16, oddimage, base-order/cardinality, native and full Transfer remain open.'
plan['repairs'] = 'Fresh successor retains failed witness01 with zero proof credit; removes two rfl tactics after rw already closes their goals. New handwritten actual order/cardinality join. Symbolic nsmul and order lemmas plus finite cardinality injection; same exact owned import closure and finite replay safeguards.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'audits': len(names), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
