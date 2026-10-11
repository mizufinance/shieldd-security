"""Preserved raw authorization body with an explicit used encoder import."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-owned-programs-20261010-01/prepare_sources.py').read_text()
text = text.replace("['ShielddNativeSdk', 'ShielddNativeScalar', 'GroupNativeSdkPreimage']", "['ShielddNativeAuthorizationRaw']")
text = text.replace("    text = source.read_text()", "    text = source.read_text()\n    assert text.startswith('import ShielddSecurity.ShielddNativeSdkRaw\\n')\n    text = 'import ShielddSecurity.ShielddNativeEncode\\n' + text")
text = text.replace('Existing owned bodies and global primitive contracts preserved.', 'Existing owned bodies and global primitive contracts preserved. Explicit used encoder import replaces the removed transitive dependency.')
ast.parse(text)
(ROOT / 'prepare_stage.py').write_text(text, encoding='utf-8', newline='\n')
print('Owned raw authorization source recipe prepared.')
