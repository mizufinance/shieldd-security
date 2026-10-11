"""Fresh explicit-coordinate-premise bridge; preserve the rejected first attempt."""
import ast
import hashlib
import json
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-native-spend-auth-20261010-01'

def pin(path):
    return {'path': str(path), 'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

records = json.loads((PRIOR / 'source-review.json').read_text())
for record in records:
    module = record['module']
    source = Path(record['candidate']['path'])
    assert pin(source) == record['candidate']
    text = source.read_text()
    if module == 'SDKNativeSpendAuth01':
        for name in ['generator_point', 'generator_order', 'generator_nonidentity', 'generator_read',
                     'canonical_multiple_nonzero', 'canonical_multiple_inverse',
                     'production_randomization', 'production_native_agreement']:
            needle = 'theorem ' + name + ' '
            assert text.count(needle) == 1
            text = text.replace(needle, 'include standard in\n' + needle, 1)
        old = "  rw [ShielddNativeSdk.spend_auth_program upstream,\n    ShielddNativeSdk.native_point_read canonical backend upstream,"
        new = "  rw [ShielddNativeSdk.spend_auth_program upstream]\n  dsimp only\n  rw [ShielddNativeSdk.native_point_read canonical backend upstream,"
        assert text.count(old) == 1
        text = text.replace(old, new)
    target = ROOT / 'handwritten' / source.name
    target.parent.mkdir(parents=True, exist_ok=True)
    assert not target.exists()
    target.write_text(text, encoding='utf-8', newline='\n')
    record['candidate'] = pin(target)
    record['predecessor_candidate'] = pin(source)
(ROOT / 'source-review.json').write_text(json.dumps(records, indent=2) + '\n')
text = (PRIOR / 'prepare.py').read_text()
text = text.replace("pin(ROOT / 'prepare_sources.py')", "pin(ROOT / 'prepare_fresh.py')")
text = text.replace("pin(ROOT / 'prepare_recipe.py')", "pin(ROOT / 'predecessor_prepare_recipe.py')")
text = text.replace("inputs += [pin(source), pin(target)]", "inputs += [pin(source), pin(target), record['predecessor_candidate']]")
text = text.replace("plan['kind'] =", "plan['pins'] += [pin(ROOT.parent / 'transfer-sdk-native-spend-auth-20261010-01' / name) for name in ['plan.json','events.jsonl','execute_bounded.py','prepare.py','source-review.json','runs/01-SDKNativeSpendAuth01/stdout.txt']]\nplan['kind'] =")
text = text.replace('Existing handwritten proof bodies preserved; complete audit inventory and bounded options only.',
                    'Fresh explicit global coordinate-binding premises for8 bridge theorems and reduction of successful Option match. Remaining owned authorization/Point bodies unchanged. Predecessor compiler rejection has zero proof/control/certification credit.')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
(ROOT / 'predecessor_prepare_recipe.py').write_bytes((PRIOR / 'prepare_recipe.py').read_bytes())
print(json.dumps({'sources': 3, 'audits': 36, 'repair': 'Explicit standard coordinate premise and Option match reduction; unchanged finite guards.',
                  'fresh_source': records[0]['candidate'], 'rejected_plan': pin(PRIOR / 'plan.json')}))
