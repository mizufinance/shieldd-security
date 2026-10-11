"""Two independent owned raw programs against full427 proof/identity floor."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-owned-programs-20261010-01/prepare.py').read_text()
text = text.replace('transfer-sdk-program-owned-floor-20261010-01', 'transfer-sdk-native-spend-auth-floor-20261010-01')
text = text.replace("floor['objects'] == 421", "floor['objects'] == 427")
text = text.replace("'owned_objects': 421", "'owned_objects': 427")
text = text.replace("'sources': 3", "'sources': 2")
text = text.replace("pin(ROOT / 'prepare_sources.py')", "pin(ROOT / 'prepare_sources.py'), pin(ROOT / 'prepare_stage.py')")
text = text.replace('OWNED_SDK_SCALAR_AND_PREIMAGE_PROGRAMS', 'OWNED_RAW_POINT_READER_AND_MULTIPLY')
text = text.replace('Three existing handwritten SDK/Scalar/preimage programs', 'Two existing handwritten raw coordinate-reader/native-multiply programs')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Two independent raw coordinate-reader/multiply bounded recipe prepared.')
