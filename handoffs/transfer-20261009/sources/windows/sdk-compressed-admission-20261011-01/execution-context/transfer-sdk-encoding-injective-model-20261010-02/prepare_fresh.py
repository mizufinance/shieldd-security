"""Fresh encoding repair; failed01 remains immutable and receives zero credit."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-encoding-injective-model-20261010-01'
assert json.loads((PRIOR / 'events.jsonl').read_text().splitlines()[-1])['result']['status'] == 'failed'
body = (PRIOR / 'handwritten/SDKEncodingInjective01.lean').read_text().split('set_option pp.all true in')[0]
old = 'ZMod.val_injective sameY'
assert body.count(old) == 1
body = body.replace(old, 'ZMod.val_injective Scalar.modulus sameY')
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/SDKEncodingInjective01.lean').write_text(body, encoding='utf-8', newline='\n')
(ROOT / 'prepare_recipe.py').write_bytes((PRIOR / 'prepare_stage.py').read_bytes())
(ROOT / 'predecessor_prepare_recipe.py').write_bytes((PRIOR / 'prepare_recipe.py').read_bytes())
print('Fresh02 supplies the explicit modulus to field representative injectivity.')
