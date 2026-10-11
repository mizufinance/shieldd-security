"""Complete408-object owned package recipe, awaiting SDK admission05 pass."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-admission-owned-floor-20261010-01/prepare.py').read_text()
old = "('transfer-concrete-admission-model-20261010-01', 1)]"
assert text.count(old) == 1
text = text.replace(old, "('transfer-concrete-admission-model-20261010-01', 1),\n          ('transfer-sdk-admission-model-20261010-05', 1),\n          ('transfer-sdk-spend-auth-certificates-20261010-01', 1)]")
text = text.replace('assert len(selected) == 406','assert len(selected) == 408')
text = text.replace('plus22 newly qualified addition/model/native-contract/cofactor/SDK arithmetic, multiplication and owned admission objects.',
                    'plus24 newly qualified addition/model/native-contract/cofactor/SDK arithmetic, multiplication, admission and SpendAuth certificate objects.')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text,encoding='utf-8',newline='\n')
print('Complete408-object first owned package recipe; copy admission only, no kernel credit.')
