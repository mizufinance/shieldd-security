"""Two independent raw SDK/encoder programs against complete429 owned package."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-owned-programs-20261010-01/prepare.py').read_text()
text = text.replace('transfer-sdk-program-owned-floor-20261010-01', 'transfer-sdk-raw-point-multiply-floor-20261010-01')
text = text.replace("floor['objects'] == 421", "floor['objects'] == 429")
text = text.replace("'owned_objects': 421", "'owned_objects': 429")
text = text.replace("'sources': 3", "'sources': 2")
text = text.replace("pin(ROOT / 'prepare_sources.py')", "pin(ROOT / 'prepare_sources.py'), pin(ROOT / 'prepare_stage.py')")
text = text.replace('OWNED_SDK_SCALAR_AND_PREIMAGE_PROGRAMS', 'OWNED_RAW_SDK_AND_ENCODER_PROGRAMS')
text = text.replace('Three existing handwritten SDK/Scalar/preimage programs', 'Two existing handwritten raw SDK/encoder programs')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Two independent raw SDK/encoder bounded recipe prepared.')
