"""Fresh parser repair: public is a reserved Lean keyword; failed02 remains zero-credit."""
import json
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-compressed-admission-model-20261010-02'
assert json.loads((PRIOR / 'events.jsonl').read_text().splitlines()[-1])['result']['status'] == 'failed'
body = (PRIOR / 'handwritten/SDKCompressedAdmission01.lean').read_text().split('set_option pp.all true in')[0]
assert len(re.findall(r'\bpublic\b', body)) == 5
body = re.sub(r'\bpublic\b', 'publicPoint', body)
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/SDKCompressedAdmission01.lean').write_text(body, encoding='utf-8', newline='\n')
(ROOT / 'prepare_recipe.py').write_bytes((PRIOR / 'prepare_recipe.py').read_bytes())
(ROOT / 'predecessor_prepare_fresh.py').write_bytes((PRIOR / 'prepare_fresh.py').read_bytes())
(ROOT / 'predecessor_prepare_recipe.py').write_bytes((PRIOR / 'predecessor_prepare_recipe.py').read_bytes())
print('Fresh03 renames the reserved public binder to publicPoint; proof statements otherwise unchanged.')
