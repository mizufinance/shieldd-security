"""Complete432 floor adds the exact owned raw authorization pass."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-raw-codec-floor-20261010-01/prepare.py').read_text()
needle = "('transfer-sdk-raw-codec-20261010-01', 2)]"
assert text.count(needle) == 1
text = text.replace(needle, "('transfer-sdk-raw-codec-20261010-01', 2),\n          ('transfer-sdk-raw-authorization-20261010-01', 1)]")
text = text.replace('len(selected) == 431', 'len(selected) == 432')
text = text.replace('plus47 qualified', 'plus48 qualified')
text = text.replace('bridge/raw coordinate reader/multiply/SDK/encoder', 'bridge/raw coordinate reader/multiply/SDK/encoder/authorization')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Complete432 floor recipe prepared; all3 raw authorization audits required.')
