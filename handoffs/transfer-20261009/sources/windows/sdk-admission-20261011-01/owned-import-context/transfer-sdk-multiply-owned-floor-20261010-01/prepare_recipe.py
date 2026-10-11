"""Prepare complete404-object floor recipe, no execution or proof credit."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-concrete-owned-floor-20261010-01/prepare.py').read_text()
old = "('transfer-sdk-extended-model-20261010-03', 1)]"
assert text.count(old) == 1
text = text.replace(old, "('transfer-sdk-extended-model-20261010-03', 1),\n          ('transfer-sdk-concrete-model-20261010-01', 1)]")
text = text.replace('assert len(selected) == 403', 'assert len(selected) == 404')
text = text.replace('plus19 newly qualified addition/model/native-contract/cofactor/SDK arithmetic objects.',
                    'plus20 newly qualified addition/model/native-contract/cofactor/SDK arithmetic and specialization objects.')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Complete404-object floor recipe; copy admission only, no proof credit.')
