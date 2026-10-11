"""Complete424 floor for SDK/base/reader/scalar/preimage source program joins."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-program-owned-floor-20261010-01/prepare.py').read_text()
needle = "('transfer-sdk-program-prerequisites-20261010-01', 2)]"
assert text.count(needle) == 1
text = text.replace(needle, "('transfer-sdk-program-prerequisites-20261010-01', 2),\n          ('transfer-sdk-owned-programs-20261010-01', 3)]")
text = text.replace('len(selected) == 421', 'len(selected) == 424')
text = text.replace('plus37 qualified', 'plus40 qualified')
text = text.replace('and owned SDK/reader prerequisites', 'and owned SDK/reader/scalar/preimage programs')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Complete424 floor recipe prepared; all53 program audits required.')
