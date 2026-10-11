"""Complete421-object floor; source/object identity grants no semantic credit."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-native-witness-owned-floor-20261010-02/prepare.py').read_text()
needle = "('transfer-sdk-native-witness-20261010-02', 1)]"
assert text.count(needle) == 1
text = text.replace(needle, "('transfer-sdk-native-witness-20261010-02', 1),\n          ('transfer-sdk-compressed-admission-model-20261010-03', 1),\n          ('transfer-sdk-spend-auth-order-20261010-01', 1),\n          ('transfer-sdk-compressed-roundtrip-20261010-01', 1),\n          ('transfer-sdk-program-prerequisites-20261010-01', 2)]")
text = text.replace('len(selected) == 416', 'len(selected) == 421')
text = text.replace('384 retained qualified cardinality/base objects plus32 newly qualified arithmetic/cofactor/admission/SDK-base/iterator/decoder/root-selection/codec-join/encoding/native-nonidentity/native-witness objects',
                    '384 retained qualified cardinality/base objects plus37 qualified concrete arithmetic/SDK/encoding/admission/native-witness/exact-SDK-base-order/roundtrip and owned SDK/reader prerequisites')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Complete421 floor recipe prepared; all five new qualified passes required.')
