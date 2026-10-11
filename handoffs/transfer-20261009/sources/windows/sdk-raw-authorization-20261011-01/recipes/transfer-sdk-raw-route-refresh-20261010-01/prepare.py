"""Update only unexecuted downstream recipes; preserve every predecessor byte."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
for task_name in ['transfer-sdk-raw-point-multiply-20261010-01',
                  'transfer-sdk-raw-point-multiply-floor-20261010-01',
                  'transfer-sdk-raw-codec-floor-20261010-01',
                  'transfer-sdk-raw-authorization-floor-20261010-01']:
    task = DIAG / task_name
    assert not (task / 'plan.json').exists() and not (task / 'composition-review.json').exists()
    source = task / 'prepare.py'
    old = source.read_text()
    text = old.replace('transfer-sdk-native-spend-auth-floor-20261010-01', 'transfer-sdk-native-spend-auth-floor-20261010-02')
    text = text.replace('transfer-sdk-native-spend-auth-20261010-01', 'transfer-sdk-native-spend-auth-20261010-02')
    assert text != old
    if not task_name.endswith('floor-20261010-01'):
        text = text.replace("plan['targets'] = targets", "plan['targets'] = targets\nplan['pins'] += [pin(ROOT / 'predecessor_prepare.py'), pin(ROOT.parent / 'transfer-sdk-raw-route-refresh-20261010-01/prepare.py')]")
    ast.parse(text)
    backup = task / 'predecessor_prepare.py'
    assert not backup.exists()
    backup.write_bytes(source.read_bytes())
    source.write_text(text, encoding='utf-8', newline='\n')
    print(task_name + ': unexecuted predecessor recipe preserved; fresh qualified bridge selected.')
