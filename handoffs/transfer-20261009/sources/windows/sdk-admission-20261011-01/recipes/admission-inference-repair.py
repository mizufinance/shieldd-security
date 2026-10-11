"""Align the canonical reader in the local multiplication invariant goal."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-sdk-admission-model-20261010-04'
body = (OLD / 'handwritten/SDKSubgroupAdmission01.lean').read_text().split('\nset_option pp.all true in\n#check')[0]
anchor = '(SDKJubjubMultiply01.encodedBits scalar)) (model.coordinates (scalar • base)) := by\n'
assert body.count(anchor) == 1
body = body.replace(anchor,anchor+'    rw [SDKJubjubMultiply01.encoded_reader]\n')
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/SDKSubgroupAdmission01.lean').write_text(body,encoding='utf-8',newline='\n')
recipe = (OLD / 'prepare_recipe.py').read_text()
recipe = recipe.replace('ast.parse(text)', 'text = text.replace("plan[\'source_repairs\'] =", "plan[\'pins\'] += [pin(DIAG / \'transfer-sdk-admission-model-20261010-04\' / name) for name in [\'plan.json\', \'events.jsonl\', \'review.json\', \'handwritten/SDKSubgroupAdmission01.lean\', \'runs/01-SDKSubgroupAdmission01/stdout.txt\']]\\nplan[\'source_repairs\'] =")\nast.parse(text)')
ast.parse(recipe)
(ROOT / 'prepare_recipe.py').write_text(recipe,encoding='utf-8',newline='\n')
print('Fresh admission05 local reader rewrite; previous four rejections retained, all guards unchanged.')
