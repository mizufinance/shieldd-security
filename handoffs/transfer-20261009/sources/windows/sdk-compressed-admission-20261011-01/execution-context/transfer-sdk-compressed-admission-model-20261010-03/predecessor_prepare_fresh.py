"""Fresh complete416 import plan; preflight-rejected01 remains immutable zero-credit."""
import ast
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-compressed-admission-model-20261010-01'
assert json.loads((PRIOR / 'events.jsonl').read_text().splitlines()[-1])['result']['status'] == 'failed'
body = (PRIOR / 'handwritten/SDKCompressedAdmission01.lean').read_text().split('set_option pp.all true in')[0]
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/SDKCompressedAdmission01.lean').write_text(body, encoding='utf-8', newline='\n')
text = (PRIOR / 'prepare_stage.py').read_text()
text = text.replace('transfer-sdk-encoding-owned-floor-20261010-01', 'transfer-sdk-native-witness-owned-floor-20261010-02')
text = text.replace("floor['objects'] == 414", "floor['objects'] == 416")
ast.parse(text)
(ROOT / 'prepare_recipe.py').write_text(text, encoding='utf-8', newline='\n')
(ROOT / 'predecessor_prepare_recipe.py').write_bytes((PRIOR / 'prepare_recipe.py').read_bytes())
print('Fresh02 unchanged admission source, corrected complete416 qualified import context.')
