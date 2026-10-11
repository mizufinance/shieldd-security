"""Fresh complete415 package for the warning-clean native nonidentity attempt."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-native-nonidentity-owned-floor-20261010-01/prepare.py').read_text()
text = text.replace('transfer-sdk-native-nonidentity-20261010-01', 'transfer-sdk-native-nonidentity-20261010-02')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Fresh complete415 package recipe.')
