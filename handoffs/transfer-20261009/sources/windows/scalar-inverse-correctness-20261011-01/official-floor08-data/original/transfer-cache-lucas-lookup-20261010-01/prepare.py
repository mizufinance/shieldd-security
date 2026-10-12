"""One read-only cache lookup; no download, compilation, or proof credit."""
import ast
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-cache-lookup-20261010-01'
def pin(p):
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
text = (PRIOR / 'execute_metadata.py').read_text().replace("assert len(plan['modules']) == 78", "assert plan['modules'] == ['Mathlib.NumberTheory.LucasPrimality']")
ast.parse(text)
(ROOT / 'execute_metadata.py').write_text(text, encoding='utf-8', newline='\n')
plan = json.loads((PRIOR / 'plan.json').read_text())
plan['modules'] = ['Mathlib.NumberTheory.LucasPrimality']
plan['command'] = plan['command'][:2] + plan['modules']
plan['pins'] += [pin(ROOT / 'execute_metadata.py'), pin(Path(__file__)), pin(PRIOR / 'plan.json')]
source = Path('C:/src/shieldd-formal/circuits/.lake/packages/mathlib/Mathlib/NumberTheory/LucasPrimality.lean')
plan['pins'].append(pin(source))
plan['scope'] += ' Exactly one module requested; cache implementation hashes its entire source graph before looking up this one existing archive. No other Lean process may overlap this metadata job.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(ROOT / 'execute_metadata.py')}))
