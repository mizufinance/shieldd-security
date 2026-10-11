"""Complete429 floor adds two independent raw-reader/multiply passes."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-native-spend-auth-floor-20261010-01/prepare.py').read_text()
needle = "('transfer-sdk-native-spend-auth-20261010-01', 3)]"
assert text.count(needle) == 1
text = text.replace(needle, "('transfer-sdk-native-spend-auth-20261010-01', 3),\n          ('transfer-sdk-raw-point-multiply-20261010-01', 2)]")
text = text.replace('len(selected) == 427', 'len(selected) == 429')
text = text.replace('plus43 qualified', 'plus45 qualified')
text = text.replace('with concrete SDK SpendAuth bridge', 'with concrete SDK SpendAuth bridge/raw coordinate reader/multiply')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Complete429 floor recipe prepared; all15 raw reader/multiply audits required.')
