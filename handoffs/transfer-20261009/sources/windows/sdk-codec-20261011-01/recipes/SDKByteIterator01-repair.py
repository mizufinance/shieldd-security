"""Fresh attempt; retain compiler-rejected01 immutable with zero proof credit."""
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-byte-iterator-model-20261010-01'
events = [json.loads(line) for line in (PRIOR / 'events.jsonl').read_text().splitlines()]
assert events[-1]['result']['status'] == 'failed'
body = (PRIOR / 'handwritten/SDKByteIterator01.lean').read_text().split('set_option pp.all true in')[0]
assert body.count('  norm_num only\n  rw [range_reader]') == 1
body = body.replace('  norm_num only\n  rw [range_reader]', '  norm_num only\n  rw [min_eq_left (by decide : 252 ≤ 256)]\n  rw [range_reader]')
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/SDKByteIterator01.lean').write_text(body,encoding='utf-8',newline='\n')
recipe = (PRIOR / 'prepare_recipe.py').read_text()
(ROOT / 'prepare_recipe.py').write_text(recipe,encoding='utf-8',newline='\n')
print('Fresh02 fixes only the final symbolic take-width simplification;01 retained.')
