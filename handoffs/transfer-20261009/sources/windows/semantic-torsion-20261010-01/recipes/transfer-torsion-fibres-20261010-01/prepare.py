"""One symbolic doubling-fibre theorem, no concrete cardinality instance."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
FLOOR = ROOT.parent / 'transfer-prerequisite-floor-20261010-06'
def pin(p):
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((FLOOR / 'plan.json').read_text())
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
source = ROOT / 'handwritten/DoublingFibre01.lean'; dest = project / source.name
shutil.copyfile(source, dest)
text = dest.read_text(); names = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
assert re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) == names
plan['targets'] = [{'module': source.stem, 'source': pin(dest), 'predecessor_source': pin(source),
    'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names}]
runner = ROOT / 'execute_bounded.py'; text = (FLOOR / 'execute_bounded.py').read_text(); ast.parse(text)
runner.write_text(text, encoding='utf-8', newline='\n')
plan['owned_imports'] = []; plan['lean_path'][0] = str(ROOT / 'project')
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(source), pin(FLOOR / 'plan.json')]
plan['kind'] = 'SYMBOLIC_DOUBLING_FIBRE_CLASSIFICATION'
plan['scope'] = 'A complete two-torsion classification yields two explicit translates for any doubling fibre in an arbitrary additive commutative group. Concrete two-torsion classification, finite bound, image parity, global cardinality and full Transfer remain open.'
plan['repairs'] = 'Small new handwritten group lemma; no source assumptions discharged by this endpoint. Exact strong import executor and fixed finite guards retained.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': len(names)}))
