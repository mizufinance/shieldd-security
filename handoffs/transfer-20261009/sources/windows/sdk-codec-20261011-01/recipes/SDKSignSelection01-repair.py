"""Fresh symbolic root-selection repair, retained failed01 remains zero-credit."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent/'transfer-sdk-sign-selection-model-20261010-01'
assert json.loads((PRIOR/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
body=(PRIOR/'handwritten/SDKSignSelection01.lean').read_text().split('set_option pp.all true in')[0]
old='  · exact positive.symm ▸ baseNonzero\n  · exact negative.symm ▸ neg_ne_zero.mpr baseNonzero'
new='''  · change root = SDKSpendAuthCertificates01.sdkBase.x at positive
    rw [positive]
    exact baseNonzero
  · change root = -SDKSpendAuthCertificates01.sdkBase.x at negative
    rw [negative]
    exact neg_ne_zero.mpr baseNonzero'''
assert old in body; body=body.replace(old,new)
(ROOT/'handwritten').mkdir(exist_ok=False)
(ROOT/'handwritten/SDKSignSelection01.lean').write_text(body,encoding='utf-8',newline='\n')
(ROOT/'prepare_recipe.py').write_bytes((PRIOR/'prepare_recipe.py').read_bytes())
print('Fresh02 explicitly projects the root coordinate before transporting nonzero.')
