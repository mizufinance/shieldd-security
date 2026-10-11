"""Complete411-object floor after qualified iterator and decoder attempts."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-spend-auth-owned-floor-20261010-01/prepare.py').read_text()
old = "('transfer-sdk-spend-auth-certificates-20261010-01', 1)]"
assert text.count(old) == 1
text = text.replace(old,"('transfer-sdk-spend-auth-certificates-20261010-01', 1),\n          ('transfer-sdk-spend-auth-join-20261010-02', 1),\n          ('transfer-sdk-byte-iterator-model-20261010-02', 1),\n          ('transfer-sdk-decoder-model-20261010-02', 1)]")
text = text.replace('assert len(selected) == 408','assert len(selected) == 411')
text = text.replace('plus24 newly qualified addition/model/native-contract/cofactor/SDK arithmetic, multiplication, admission and SpendAuth certificate objects.', 'plus27 newly qualified arithmetic/cofactor/admission/SDK-base/iterator/decoder objects.')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text,encoding='utf-8',newline='\n')
print('Complete411-object first owned package recipe, gated on actual qualified passes.')
