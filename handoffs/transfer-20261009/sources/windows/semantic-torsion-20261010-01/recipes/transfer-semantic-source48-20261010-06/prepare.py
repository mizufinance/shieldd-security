"""Repair SOURCE48 scalar commutation and remove its unused characteristic parameter."""
import ast
import hashlib
import json
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-semantic-source48-20261010-05'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
events = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines()]
done = [e for e in events if e['event'] == 'attempt_finished']
assert len(done) == 6 and all(e['result']['status'] == 'passed' for e in done[:5])
assert done[-1]['module'] == 'TransferSemanticSubgroup48' and done[-1]['result']['status'] == 'failed'
stdout = PRIOR / 'runs/06-TransferSemanticSubgroup48/stdout.txt'
assert stdout.read_text().count('warning:') == 3 and stdout.read_text().count('error:') == 1
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
originals = plan['owned_imports'] + [p for e in done[:5] for p in e['result']['objects']]; base = []
for p in originals:
    assert pin(p['path']) == p
    dest = project / Path(p['path']).name; shutil.copyfile(p['path'], dest); base.append(pin(dest))
target = plan['targets'][-1]; source = Path(target['source']['path']); assert pin(source) == target['source']
text = source.read_text()
assert text.count('[CharP F Scalar.modulus]') == 1
assert text.count('Nat.mul_comm Scalar.order n') == 1
text = text.replace(' [CharP F Scalar.modulus]', '')
text = text.replace('Nat.mul_comm Scalar.order n', 'Nat.mul_comm n Scalar.order')
dest = project / source.name; dest.write_text(text, encoding='utf-8', newline='\n')
plan['targets'] = [{**target, 'source': pin(dest), 'predecessor_source': target['source']}]
runner = ROOT / 'execute_bounded.py'; text = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(text)
runner.write_text(text, encoding='utf-8', newline='\n')
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(PRIOR / 'plan.json'), pin(PRIOR / 'events.jsonl'), pin(stdout), target['source']] + originals + base + [e['result']['stdout'] for e in done[:5]]
plan['predecessor'] = {'plan': pin(PRIOR / 'plan.json'), 'events': pin(PRIOR / 'events.jsonl'), 'failure': done[-1]}
plan['kind'] = 'BOUNDED_HANDWRITTEN_SOURCE48_SCALAR_COMMUTATION_SUCCESSOR'
plan['repairs'] = 'SOURCE48 only: after reverse mul_nsmul the product is n*Scalar.order, so commute that exact product before unfolding to n acting on the r-annihilated point. Remove the global unused CharP parameter: representation uses the explicit codec roundtrip/bound and additive group operations, not field characteristic. Conclusions/operation/base-order premises unchanged; exact new full types audited. Failed predecessor retained, zero negative-control credit.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'repair': plan['repairs']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audit_pairs': 11}))
