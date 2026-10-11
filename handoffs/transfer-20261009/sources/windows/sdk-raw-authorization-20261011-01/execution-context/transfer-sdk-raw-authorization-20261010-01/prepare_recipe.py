"""One named raw authorization module against complete431 package."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-owned-programs-20261010-01/prepare.py').read_text()
text = text.replace('transfer-sdk-program-owned-floor-20261010-01', 'transfer-sdk-raw-codec-floor-20261010-01')
text = text.replace("floor['objects'] == 421", "floor['objects'] == 431")
text = text.replace("'owned_objects': 421", "'owned_objects': 431")
text = text.replace("'sources': 3", "'sources': 1")
text = text.replace("pin(ROOT / 'prepare_sources.py')", "pin(ROOT / 'prepare_sources.py'), pin(ROOT / 'prepare_stage.py')")
text = text.replace('OWNED_SDK_SCALAR_AND_PREIMAGE_PROGRAMS', 'OWNED_RAW_AUTHORIZATION_PROGRAM')
text = text.replace('Three existing handwritten SDK/Scalar/preimage programs', 'One existing handwritten raw authorization program')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Raw authorization bounded recipe prepared.')
