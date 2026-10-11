"""Split handwritten arithmetic from concrete imports; retain memory rejection02."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-sdk-extended-model-20261010-02'
body = (OLD / 'handwritten/SDKJubjubExtended01.lean').read_text().split('\nset_option pp.all true in\n#check')[0]
cut = body.index('\ntheorem concrete_double')
arithmetic = body[:cut].replace('import ShielddSecurity.ConcreteCofactorModel01\n', '') + '\n\nend ShielddSecurity.SDKJubjubExtended01\n'
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/SDKJubjubExtended01.lean').write_text(arithmetic, encoding='utf-8', newline='\n')
bridge = ROOT.parent / 'transfer-sdk-concrete-model-20261010-01/handwritten'
bridge.mkdir(parents=True, exist_ok=False)
concrete = body[cut:].replace('end ShielddSecurity.SDKJubjubExtended01', 'end ShielddSecurity.SDKJubjubConcrete01')
prefix = 'import ShielddSecurity.SDKJubjubExtended01\nimport ShielddSecurity.ConcreteCofactorModel01\n\nset_option autoImplicit false\nset_option maxHeartbeats 300000\nset_option maxRecDepth 4096\n\nnamespace ShielddSecurity.SDKJubjubConcrete01\nopen ShielddSecurity.SDKJubjubExtended01\n'
(bridge / 'SDKJubjubConcrete01.lean').write_text(prefix + concrete, encoding='utf-8', newline='\n')
recipe = (OLD / 'prepare_recipe.py').read_text()
recipe = recipe.replace("'imports': ['ShielddSecurity.GroupNativeMultiply', 'ShielddSecurity.ConcreteCofactorModel01']", "'imports': ['ShielddSecurity.GroupNativeMultiply']")
recipe = recipe.replace("pin(ROOT / 'repair_recipe.py')", "pin(ROOT / 'split_recipe.py')")
recipe = recipe.replace('and proves actual concrete curve addition/doubling.', 'and proves symbolic affine addition/doubling; concrete specialization is separately scheduled.')
insertion = "text = text.replace(\"plan['source_repairs'] =\", \"plan['pins'] += [pin(DIAG / 'transfer-sdk-extended-model-20261010-02' / name) for name in ['events.jsonl', 'plan.json', 'review.json', 'handwritten/SDKJubjubExtended01.lean', 'runs/01-SDKJubjubExtended01/stdout.txt']]\\nplan['source_repairs'] =\")\n"
recipe = recipe.replace('ast.parse(text)', insertion + 'ast.parse(text)')
ast.parse(recipe)
(ROOT / 'prepare_recipe.py').write_text(recipe, encoding='utf-8', newline='\n')
print('Fresh arithmetic03 and unprepared concrete01 handwritten split; memory guards unchanged.')
