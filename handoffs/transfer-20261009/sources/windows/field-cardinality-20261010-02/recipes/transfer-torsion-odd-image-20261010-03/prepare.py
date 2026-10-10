"""One narrow finite-group kernel/image cardinality join."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-modular-power-field-20261010-01'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
base = []
for record in plan['owned_imports']:
    assert pin(record['path']) == record
    dest = project / Path(record['path']).name; shutil.copyfile(record['path'], dest); base.append(pin(dest))
source = ROOT / 'handwritten/TorsionOddImage01.lean'
dest = project / source.name; shutil.copyfile(source, dest)
text = source.read_text(); names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert names == re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M)
runner = ROOT / 'execute_bounded.py'; source_runner = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(source_runner)
runner.write_text(source_runner, encoding='utf-8', newline='\n')
floor = DIAG / 'transfer-external-floor-complete-20261010-09/external-floor.json'
assert json.loads(floor.read_text())['admission_ready']
plan['external_floor'] = {**pin(floor), 'admission_ready': True}
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source), 'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['lean_path'].insert(1, str(DIAG / 'transfer-external-package-overlay-20261010-03/modules'))
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(floor)] + base
plan['pins'] += [pin(ROOT / 'prepare_repair.py'), pin(DIAG / 'transfer-torsion-odd-image-20261010-02/events.jsonl'), pin(DIAG / 'transfer-torsion-odd-image-20261010-02/handwritten/TorsionOddImage01.lean')]
plan['kind'] = 'CAUCHY_EIGHT_IMAGE_ODDNESS_JOIN'
plan['scope'] = 'Two small additive group theorems: a nonzero eight-image two-torsion point lifts to order16; absence of order16 implies odd eight-image cardinality by Cauchy. Actual curve order16 exclusion, torsion enumeration and concrete binding, native and full Transfer remain open.'
plan['repairs'] = 'Two new small handwritten Cauchy/image lemmas, unchanged finite guards and complete current import inventory.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
