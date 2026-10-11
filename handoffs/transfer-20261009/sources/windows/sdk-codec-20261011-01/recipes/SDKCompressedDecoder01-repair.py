"""Fresh decoder proof repairs; rejected01 remains immutable and zero-credit."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-decoder-model-20261010-01'
events = [json.loads(line) for line in (PRIOR / 'events.jsonl').read_text().splitlines()]
assert events[-1]['result']['status'] == 'failed'
body = (PRIOR / 'handwritten/SDKCompressedDecoder01.lean').read_text().split('set_option pp.all true in')[0]
body = body.replace('_ = 1 := by linear_combination zero', '_ = 1 := by linear_combination -zero')
old = '  · cases point; cases SDKSpendAuthCertificates01.sdkBase\n    simp_all'
new = '''  · have extensionality : ∀ (left right : Group.Point F),
        left.x = right.x → left.y = right.y → left = right := by
      intro left right hx hy
      cases left
      cases right
      congr 1
    exact extensionality point SDKSpendAuthCertificates01.sdkBase sameX sameY'''
assert old in body; body = body.replace(old,new)
body = body.replace('simpa only [pow_two] using','simpa only [pow_two, mul_assoc] using')
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/SDKCompressedDecoder01.lean').write_text(body,encoding='utf-8',newline='\n')
(ROOT / 'prepare_recipe.py').write_text((PRIOR / 'prepare_recipe.py').read_text(),encoding='utf-8',newline='\n')
print('Fresh02 fixes a linear-combination sign, constructor extensionality and multiplication association.')
