"""Complete431 floor adds two independent raw SDK/encoder passes."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-raw-point-multiply-floor-20261010-01/prepare.py').read_text()
needle = "('transfer-sdk-raw-point-multiply-20261010-01', 2)]"
assert text.count(needle) == 1
text = text.replace(needle, "('transfer-sdk-raw-point-multiply-20261010-01', 2),\n          ('transfer-sdk-raw-codec-20261010-01', 2)]")
text = text.replace('len(selected) == 429', 'len(selected) == 431')
text = text.replace('plus45 qualified', 'plus47 qualified')
text = text.replace('bridge/raw coordinate reader/multiply', 'bridge/raw coordinate reader/multiply/SDK/encoder')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Complete431 floor recipe prepared; all17 raw SDK/encoder audits required.')
