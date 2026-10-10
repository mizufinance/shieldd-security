"""Connect only fully audited prime-tree outputs to the concrete field lemmas.

Run after all five disjoint prime batches succeed. This script refuses a partial
tree and checks shared owned-object identities before copying its exact closure.
"""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-torsion-prime-nonsquare-20261010-04'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
originals = {}; receipts = []; qualified_modules = []
for task in [PRIOR] + [DIAG / ('transfer-prime-tree-closed-20261010-%02d' % n) for n in range(1, 6)]:
    previous = json.loads((task / 'plan.json').read_text())
    events = [json.loads(x) for x in (task / 'events.jsonl').read_text().splitlines()]
    done = [e for e in events if e['event'] == 'attempt_finished']
    assert len(done) == len(previous['targets']) and all(e['result']['status'] == 'passed' for e in done)
    qualified_modules += [e['module'] for e in done]
    for r in previous['owned_imports'] + [p for e in done for p in e['result']['objects']]:
        assert pin(r['path']) == r
        key = Path(r['path']).name
        if key in originals: assert originals[key]['sha256'] == r['sha256'], key
        originals[key] = r
    receipts += [pin(task / 'plan.json'), pin(task / 'events.jsonl')] + [e['result']['stdout'] for e in done]
assert qualified_modules == ['TorsionPrimeNonsquare01', 'LucasCertificate'] + ['FieldPrimeNode%02d' % n for n in range(1, 39)]
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
base = []
for key, r in originals.items():
    dest = project / key; shutil.copyfile(r['path'], dest); base.append(pin(dest))
source = ROOT / 'handwritten/TorsionCertifiedField01.lean'; dest = project / source.name
shutil.copyfile(source, dest)
text = source.read_text(); names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert names == re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M)
runner = ROOT / 'execute_bounded.py'; body = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(body)
runner.write_text(body, encoding='utf-8', newline='\n')
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source), 'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(DIAG / 'transfer-prime-tree-replay-20261010-02/generation-review.json')] + list(originals.values()) + base + receipts
plan['kind'] = 'CONCRETE_CERTIFIED_PRIME_FIELD_TORSION_ALGEBRA'
plan['scope'] = 'Closed actual modulus primality, concrete Euler nonsquares, nonzero B, discriminant scaling and Y=0 algebra for A40962/B-40964. No assumed prime fact in final conclusions. Actual Point two-torsion classification, exhaustive eight-torsion/halves, curve cardinality, native and full Transfer remain open.'
plan['repairs'] = 'One new handwritten actual-field join after all generated prime-tree nodes and conditional Euler source succeed. Complete exact owned closure and unchanged finite guards.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'audits': len(names), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
