"""Update only unexecuted floor recipes to the fresh strict raw-reader successor."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
for task_name in ['transfer-sdk-raw-point-multiply-floor-20261010-01',
                  'transfer-sdk-raw-codec-floor-20261010-01',
                  'transfer-sdk-raw-authorization-floor-20261010-01']:
    task = ROOT.parent / task_name
    assert not (task / 'composition-review.json').exists()
    source = task / 'prepare.py'
    old = source.read_text()
    text = old.replace('transfer-sdk-raw-point-multiply-20261010-01', 'transfer-sdk-raw-point-multiply-20261010-02')
    assert text != old
    text = text.replace("'superseded_unrun_partition_recipe':", "'unexecuted_reader_predecessor_recipe': pin(ROOT / 'predecessor_prepare01.py'),\n               'route_refresh_recipe': pin(DIAG / 'transfer-sdk-raw-route-refresh-20261010-02/prepare.py'),\n               'superseded_unrun_partition_recipe':")
    ast.parse(text)
    backup = task / 'predecessor_prepare01.py'
    assert not backup.exists()
    backup.write_bytes(source.read_bytes())
    source.write_text(text, encoding='utf-8', newline='\n')
    print(task_name + ': unexecuted floor recipe preserved; strict raw-reader successor selected.')
