"""One generic Euler-to-nonsquare algebra lemma against the corrected inventory."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-torsion-cardinality49-20261010-03'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
events = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines()]
algebra = next(e for e in events if e['event'] == 'attempt_finished' and e['module'] == 'WeierstrassTwoTorsionAlgebra01')
assert algebra['result']['status'] == 'passed'
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
originals = plan['owned_imports'] + algebra['result']['objects']; base = []
for p in originals:
    assert pin(p['path']) == p
    dest = project / Path(p['path']).name; shutil.copyfile(p['path'], dest); base.append(pin(dest))
source = ROOT / 'handwritten/EulerNonsquare01.lean'
dest = project / source.name; shutil.copyfile(source, dest)
text = dest.read_text()
names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) == names
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source),
    'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
runner = ROOT / 'execute_bounded.py'
text = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(text)
runner.write_text(text, encoding='utf-8', newline='\n')
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(PRIOR / 'plan.json'), pin(PRIOR / 'events.jsonl'), algebra['result']['stdout']] + originals + base
plan['kind'] = 'SYMBOLIC_EULER_NONSQUARE_JOIN'
plan['scope'] = 'One algebra theorem under explicit nonzero, characteristic-not-two, Fermat exponent and Euler residue premises. No actual prime-field instance, integer-to-field correspondence, torsion enumeration, native or full Transfer certification.'
plan['repairs'] = 'New small handwritten algebra lemma. Complete Range/Spend/algebra owned import closure copied from qualified sources. Finite guards unchanged.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
