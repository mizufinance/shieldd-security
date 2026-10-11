"""Fresh427 package recipe, retaining the unexecuted predecessor candidate."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-sdk-native-spend-auth-floor-20261010-01'
text = (PRIOR / 'prepare.py').read_text()
text = text.replace('transfer-sdk-native-spend-auth-20261010-01', 'transfer-sdk-native-spend-auth-20261010-02')
text = text.replace("'superseded_unrun_partition_recipe':", "'superseded_unrun_bridge_recipe': pin(DIAG / 'transfer-sdk-native-spend-auth-floor-20261010-01/prepare.py'),\n               'superseded_unrun_partition_recipe':")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Fresh complete427 package recipe prepared; only explicit-premise qualified bridge admitted.')
