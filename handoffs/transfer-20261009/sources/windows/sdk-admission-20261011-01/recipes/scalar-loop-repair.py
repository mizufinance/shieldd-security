"""Align byte-reader rewrite in the modulus-test goal; preserve rejected02."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-sdk-multiply-model-20261010-02'
body = (OLD / 'handwritten/SDKJubjubMultiply01.lean').read_text().split('\nset_option pp.all true in\n#check')[0]
old = '  have represented := multiply_represents base p baseRep (encodedBits Scalar.order)'
assert body.count(old) == 1
body = body.replace(old, '  rw [encoded_reader]\n' + old)
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/SDKJubjubMultiply01.lean').write_text(body, encoding='utf-8', newline='\n')
recipe = (OLD / 'prepare_recipe.py').read_text()
recipe = recipe.replace('ast.parse(text)', 'text = text.replace("plan[\'source_repairs\'] =", "plan[\'pins\'] += [pin(DIAG / \'transfer-sdk-multiply-model-20261010-02\' / name) for name in [\'plan.json\', \'events.jsonl\', \'review.json\', \'handwritten/SDKJubjubMultiply01.lean\', \'runs/01-SDKJubjubMultiply01/stdout.txt\']]\\nplan[\'source_repairs\'] =")\nast.parse(text)')
ast.parse(recipe)
(ROOT / 'prepare_recipe.py').write_text(recipe, encoding='utf-8', newline='\n')
print('Fresh scalar-loop03 handwritten rewrite repair; finite and physical guards unchanged.')
