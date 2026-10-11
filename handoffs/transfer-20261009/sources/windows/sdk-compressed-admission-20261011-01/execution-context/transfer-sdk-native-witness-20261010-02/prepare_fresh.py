"""Fresh native witness source, using the warning-clean complete415 context."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-native-witness-20261010-01'
assert not (PRIOR / 'plan.json').exists()
body = (PRIOR / 'handwritten/GroupNativeSubgroupWitness.lean').read_text().split('set_option pp.all true in')[0]
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/GroupNativeSubgroupWitness.lean').write_text(body, encoding='utf-8', newline='\n')
text = (PRIOR / 'prepare_stage.py').read_text()
text = text.replace('transfer-sdk-native-nonidentity-owned-floor-20261010-01', 'transfer-sdk-native-nonidentity-owned-floor-20261010-02')
ast.parse(text)
(ROOT / 'prepare_recipe.py').write_text(text, encoding='utf-8', newline='\n')
(ROOT / 'predecessor_prepare_recipe.py').write_bytes((PRIOR / 'prepare_recipe.py').read_bytes())
print('Fresh four-audit native witness recipe prepared.')
