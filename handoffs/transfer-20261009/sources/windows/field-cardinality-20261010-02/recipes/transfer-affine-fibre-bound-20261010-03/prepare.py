"""One finite field/Euler join with its explicit primality premise audited."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-modular-power-field-20261010-01'
ALGEBRA = DIAG / 'transfer-torsion-euler-field-20261010-01'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
originals = {}
for task in [PRIOR, ALGEBRA]:
    previous = json.loads((task / 'plan.json').read_text())
    events = [json.loads(x) for x in (task / 'events.jsonl').read_text().splitlines()]
    done = [e for e in events if e['event'] == 'attempt_finished']
    assert len(done) == len(previous['targets']) and all(e['result']['status'] == 'passed' for e in done)
    for record in previous['owned_imports'] + [p for e in done for p in e['result']['objects']]:
        assert pin(record['path']) == record
        key = Path(record['path']).name
        if key in originals: assert originals[key]['sha256'] == record['sha256']
        originals[key] = record
    plan['pins'] += [pin(task / 'plan.json'), pin(task / 'events.jsonl')] + [e['result']['stdout'] for e in done]
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
base = []
for key, record in originals.items():
    dest = project / key; shutil.copyfile(record['path'], dest); base.append(pin(dest))
source = ROOT / 'handwritten/AffineFibreBound01.lean'
dest = project / source.name; shutil.copyfile(source, dest)
text = source.read_text(); names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) == names
runner = ROOT / 'execute_bounded.py'; text_runner = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(text_runner)
runner.write_text(text_runner, encoding='utf-8', newline='\n')
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source),
    'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source)] + list(originals.values()) + base
floor = DIAG / 'transfer-external-floor-complete-20261010-09/external-floor.json'
assert json.loads(floor.read_text())['admission_ready']
plan['external_floor'] = {**pin(floor), 'admission_ready': True}
plan['lean_path'].insert(1, str(DIAG / 'transfer-external-package-overlay-20261010-03/modules'))
plan['pins'] += [pin(floor), pin('C:\\src\\shieldd-formal\\.work\\diagnostics\\transfer-affine-fibre-bound-20261010-02\\prepare_repair.py')]
plan['pins'] += [pin(DIAG / 'transfer-affine-fibre-bound-20261010-01/events.jsonl'), pin(DIAG / 'transfer-affine-fibre-bound-20261010-01/handwritten/AffineFibreBound01.lean')]
plan['pins'] += [pin('C:\\src\\shieldd-formal\\.work\\diagnostics\\transfer-cardinality-repairs-20261010-01\\prepare.py'), pin('C:\\src\\shieldd-formal\\.work\\diagnostics\\transfer-affine-fibre-bound-20261010-02\\events.jsonl'), pin('C:\\src\\shieldd-formal\\.work\\diagnostics\\transfer-affine-fibre-bound-20261010-02\\handwritten\\AffineFibreBound01.lean'), pin('C:\\src\\shieldd-formal\\.work\\diagnostics\\transfer-affine-fibre-bound-20261010-02\\runs\\01-AffineFibreBound01\\stdout.txt')]
plan['kind'] = 'SYMBOLIC_AFFINE_FIBRE_CARDINALITY_BOUND'
plan['scope'] = 'Every square-equation fibre in an explicit finite field has at most two solutions. Arbitrary Y-square affine solution sets have at most 2*card(field), and adjoining the point at infinity adds one. Exact curve equation/point-set binding, torsion/cardinality/native/full Transfer remain open.'
plan['repairs'] = 'Four new handwritten finite-field fibre count declarations. Owned transitive import closure merged from two qualified jobs, identical shared objects checked. Finite guards unchanged.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
