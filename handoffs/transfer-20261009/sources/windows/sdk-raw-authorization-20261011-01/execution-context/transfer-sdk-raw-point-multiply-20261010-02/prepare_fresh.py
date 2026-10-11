"""Fresh strict raw reader: remove only the unused case-equation simp argument."""
import ast
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-raw-point-multiply-20261010-01'

def pin(path):
    return {'path': str(path), 'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

records = json.loads((PRIOR / 'source-review.json').read_text())
for record in records:
    source = Path(record['candidate']['path'])
    assert pin(source) == record['candidate']
    text = source.read_text()
    if record['module'] == 'ShielddNativeReadPoint':
        old = 'refine ⟨output,by simp only [checked],?_⟩'
        assert text.count(old) == 1
        text = text.replace(old, 'refine ⟨output,rfl,?_⟩')
    target = ROOT / 'handwritten' / source.name
    target.parent.mkdir(parents=True, exist_ok=True)
    assert not target.exists()
    target.write_text(text, encoding='utf-8', newline='\n')
    record['candidate'] = pin(target)
    record['predecessor_candidate'] = pin(source)
(ROOT / 'source-review.json').write_text(json.dumps(records, indent=2) + '\n')
text = (PRIOR / 'prepare.py').read_text()
text = text.replace("pin(ROOT / 'prepare_sources.py')", "pin(ROOT / 'prepare_fresh.py')")
text = text.replace("pin(ROOT / 'prepare_stage.py')", "pin(ROOT / 'predecessor_prepare_stage.py')")
text = text.replace("pin(ROOT / 'prepare_recipe.py')", "pin(ROOT / 'predecessor_prepare_recipe.py')")
text = text.replace("pin(ROOT / 'predecessor_prepare.py')", "pin(ROOT / 'rejected_prepare.py')")
text = text.replace("inputs += [pin(source), pin(target), record['prior_handwritten']]", "inputs += [pin(source), pin(target), record['prior_handwritten'], record['predecessor_candidate']]")
text = text.replace("plan['kind'] =", "plan['pins'] += [pin(ROOT.parent / 'transfer-sdk-raw-point-multiply-20261010-01' / name) for name in ['plan.json','events.jsonl','execute_bounded.py','prepare.py','source-review.json','runs/01-ShielddNativeReadPoint/stdout.txt']]\nplan['kind'] =")
text = text.replace('Existing handwritten proof bodies preserved; complete audit inventory and bounded options only.',
                    'Fresh raw reader replaces only unused case-equation simplifier argument with reflexivity. Multiply body unchanged. Prior strict-warning rejection has zero proof/control/certification credit; finite guards unchanged.')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
for old, new in [('prepare_stage.py','predecessor_prepare_stage.py'), ('prepare_recipe.py','predecessor_prepare_recipe.py'), ('predecessor_prepare.py','rejected_prepare.py')]:
    (ROOT / new).write_bytes((PRIOR / old).read_bytes())
print(json.dumps({'sources': 2, 'audits': 15, 'repair': 'Unused checked simp argument replaced by reflexivity; unchanged statements/primitive contracts/guards.',
                  'fresh_source': records[0]['candidate'], 'rejected_plan': pin(PRIOR / 'plan.json')}))
