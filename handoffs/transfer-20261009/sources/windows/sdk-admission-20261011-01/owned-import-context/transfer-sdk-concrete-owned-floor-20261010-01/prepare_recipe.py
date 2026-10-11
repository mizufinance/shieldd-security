"""Prepare complete403-object copy recipe; execute only after arithmetic03 passes."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-admission-owned-floor-20261010-01/prepare.py'
text = prior.read_text()
old = "('transfer-concrete-cofactor-model-20261010-02', 1)]"
assert text.count(old) == 1
text = text.replace(old, "('transfer-concrete-cofactor-model-20261010-02', 1),\n          ('transfer-sdk-extended-model-20261010-03', 1)]")
text = text.replace('assert len(selected) == 402', 'assert len(selected) == 403')
text = text.replace('plus18 newly qualified addition/model/native-contract/cofactor objects.',
                    'plus19 newly qualified addition/model/native-contract/cofactor/SDK arithmetic objects.')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Complete403-object floor recipe; copy admission only, no proof credit.')
