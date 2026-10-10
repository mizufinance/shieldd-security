"""Pin a one-module actual coordinate bridge after the actual doubling endpoint passes."""
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
parser.add_argument('--prior-task', required=True)
args = parser.parse_args()
assert re.fullmatch(r'transfer-concrete-point-doubling-20261010-[0-9]{2}', args.prior_task)
PRIOR = DIAG / args.prior_task
def pin(p):
    p = Path(p)
    with p.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
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
    dest = project / Path(r['path']).name
    shutil.copyfile(r['path'], dest); base.append(pin(dest))
source = ROOT / 'handwritten/ConcretePointCoordinateRows01.lean'
dest = project / source.name; shutil.copyfile(source, dest)
text = source.read_text()
names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert names == re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) and len(names) == 6
runner = ROOT / 'execute_bounded.py'
body = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(body)
runner.write_text(body, encoding='utf-8', newline='\n')
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source),
    'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(ROOT / 'prepare_source.py'),
    pin(PRIOR / 'plan.json'), pin(PRIOR / 'events.jsonl'), done[0]['result']['stdout']] + originals + base
for name in ['ConcretePointOperationRows01', 'ConcreteIntegerCertificates01']:
    plan['pins'].append(pin(Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity') / (name + '.lean')))
plan['kind'] = 'ACTUAL_POINT_COORDINATE_ROWS_AND_INTEGER_CERTIFICATE_CASTS'
plan['scope'] = 'Kernel-checked integer congruences imply equality/nonzero in the actual certified field. Actual secant/tangent/vertical coordinate constraints imply actual Mathlib Point addition. Generated candidate certificates and exact eight-torsion/exhaustiveness/no16/cardinality, native and full Transfer remain open.'
plan['repairs'] = 'Adapt published handwritten row bridge to certified actual field/point. Same complete import floor and finite executor guards.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'audits': len(names), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
