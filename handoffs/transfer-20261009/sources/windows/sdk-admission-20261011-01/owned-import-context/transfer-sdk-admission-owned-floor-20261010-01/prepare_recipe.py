"""Prepare complete406-object copy recipe; scalar-loop pass is required."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-multiply-owned-floor-20261010-01/prepare.py').read_text()
old = "('transfer-sdk-concrete-model-20261010-01', 1)]"
assert text.count(old) == 1
text = text.replace(old, "('transfer-sdk-concrete-model-20261010-01', 1),\n          ('transfer-sdk-multiply-model-20261010-03', 1),\n          ('transfer-concrete-admission-model-20261010-01', 1)]")
text = text.replace('assert len(selected) == 404', 'assert len(selected) == 406')
text = text.replace('plus20 newly qualified addition/model/native-contract/cofactor/SDK arithmetic and specialization objects.',
                    'plus22 newly qualified addition/model/native-contract/cofactor/SDK arithmetic, multiplication and owned admission objects.')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Complete406-object copy recipe; no new proof credit.')
