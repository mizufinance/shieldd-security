"""Repair only the additive-group lemma name; preserve the rejected attempt."""
import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-raw-authorization-join-20261010-01'

def pin(path):
    return {'path': str(path), 'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

source = PRIOR / 'handwritten/SDKRawAuthorization01.lean'
text = source.read_text()
old = 'rw [nsmul_neg, SDKSpendAuthSubgroup01.base_subgroup, neg_zero]'
new = 'rw [neg_nsmul, SDKSpendAuthSubgroup01.base_subgroup, neg_zero]'
assert text.count(old) == 1
text = text.replace(old, new)
target = ROOT / 'handwritten' / source.name
target.parent.mkdir(parents=True, exist_ok=True)
assert not target.exists()
target.write_text(text, encoding='utf-8', newline='\n')
records = [{'module': 'SDKRawAuthorization01', 'predecessor_candidate': pin(source),
            'candidate': pin(target), 'repair': 'nsmul_neg order lemma replaced by neg_nsmul additive-group equality',
            'rejected_attempt_credit': 0, 'semantic_negative_control_credit': 0}]
(ROOT / 'source-review.json').write_text(json.dumps(records, indent=2) + '\n')
for name in ['prepare_recipe.py', 'prepare_recipe02.py', 'prepare_recipe03.py', 'prepare_recipe04.py',
             'predecessor_prepare_stage03.py', 'predecessor_prepare_stage.py']:
    (ROOT / name).write_bytes((PRIOR / name).read_bytes())
recipe = (PRIOR / 'prepare.py').read_text()
recipe = recipe.replace("pin(Path(__file__)),", "pin(Path(__file__)), pin(ROOT / 'prepare_fresh.py'), pin(ROOT / 'source-review.json'),")
recipe = recipe.replace("plan['kind'] =", "plan['pins'] += [pin(ROOT.parent / 'transfer-sdk-raw-authorization-join-20261010-01' / name) for name in ['plan.json','events.jsonl','execute_bounded.py','prepare.py','handwritten/SDKRawAuthorization01.lean','runs/01-SDKRawAuthorization01/stdout.txt']]\nplan['kind'] =")
recipe = recipe.replace('New handwritten input-boundary proof; no generated edits or new axioms.',
    'Fresh additive-group neg_nsmul lemma-name repair. Failed predecessor preserved with zero proof/control/certification credit; finite guards unchanged.')
ast.parse(recipe)
(ROOT / 'prepare.py').write_text(recipe, encoding='utf-8', newline='\n')
print(json.dumps({'candidate': pin(target), 'rejected_plan': pin(PRIOR / 'plan.json'), 'audits': 13, 'guard_changes': False}))
