"""Two independent raw SDK and encoder programs, preserved source bodies."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-owned-programs-20261010-01/prepare_sources.py').read_text()
text = text.replace("['ShielddNativeSdk', 'ShielddNativeScalar', 'GroupNativeSdkPreimage']", "['ShielddNativeEncode', 'ShielddNativeSdkRaw']")
ast.parse(text)
(ROOT / 'prepare_stage.py').write_text(text, encoding='utf-8', newline='\n')
print('Two owned raw SDK/encoder source recipes prepared.')
