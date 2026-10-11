"""Remove one unused simp argument; warning-rejected01 retains zero credit."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-native-nonidentity-20261010-01'
assert json.loads((PRIOR / 'events.jsonl').read_text().splitlines()[-1])['result']['status'] == 'failed'
body = (PRIOR / 'handwritten/GroupNativeNonidentity.lean').read_text().split('set_option pp.all true in')[0]
assert body.count('zero,mul_zero,zero_mul,zero_add,add_zero') == 1
body = body.replace('zero,mul_zero,zero_mul,zero_add,add_zero', 'zero,mul_zero,zero_mul,add_zero')
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/GroupNativeNonidentity.lean').write_text(body, encoding='utf-8', newline='\n')
(ROOT / 'prepare_recipe.py').write_bytes((PRIOR / 'prepare_stage.py').read_bytes())
(ROOT / 'predecessor_prepare_recipe.py').write_bytes((PRIOR / 'prepare_recipe.py').read_bytes())
print('Fresh02 removes only the unused zero_add argument, preserving conclusions and premises.')
