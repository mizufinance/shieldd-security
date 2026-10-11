"""Fresh complete414 package, conditional on three qualified codec successors."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-codec-owned-floor-20261010-01/prepare.py').read_text()
old = "('transfer-sdk-decoder-model-20261010-02', 1)]"
assert text.count(old) == 1
text = text.replace(old, "('transfer-sdk-decoder-model-20261010-02', 1),\n          ('transfer-sdk-sign-selection-model-20261010-02', 1),\n          ('transfer-sdk-codec-join-20261010-01', 1),\n          ('transfer-sdk-encoding-injective-model-20261010-02', 1)]")
text = text.replace('assert len(selected) == 411', 'assert len(selected) == 414')
text = text.replace('plus27 newly qualified arithmetic/cofactor/admission/SDK-base/iterator/decoder objects.', 'plus30 newly qualified arithmetic/cofactor/admission/SDK-base/iterator/decoder/root-selection/codec-join/encoding objects.')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Complete414-object first owned package recipe; actual qualified passes remain mandatory.')
