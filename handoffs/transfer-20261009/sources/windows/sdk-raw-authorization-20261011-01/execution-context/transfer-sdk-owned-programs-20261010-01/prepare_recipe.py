"""Adapt the unchanged bounded prerequisite recipe to complete421 dependencies."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
text = (ROOT.parent / 'transfer-sdk-program-prerequisites-20261010-01/prepare.py').read_text()
text = text.replace('transfer-sdk-native-witness-owned-floor-20261010-02', 'transfer-sdk-program-owned-floor-20261010-01')
text = text.replace("floor['objects'] == 416", "floor['objects'] == 421")
text = text.replace("'owned_objects': 416", "'owned_objects': 421")
text = text.replace("'sources': 2", "'sources': 3")
text = text.replace("plan['targets'] = targets", "plan['targets'] = targets\nplan['owned_import_pool'] = pin(POOL / 'composition-review.json')\nplan['owned_imports'] = owned\nplan['pins'] += floor['input_records'] + owned + [pin(POOL / 'composition-review.json'), pin(POOL / 'prepare.py'), pin(POOL / 'prepare_recipe.py')]")
text = text.replace("pin(ROOT / 'source-review.json'), pin(runner)", "pin(ROOT / 'source-review.json'), pin(ROOT / 'prepare_recipe.py'), pin(runner)")
text = text.replace('OWNED_SDK_PROGRAM_PREREQUISITES', 'OWNED_SDK_SCALAR_AND_PREIMAGE_PROGRAMS')
text = text.replace('Two existing handwritten SDK/coordinate-reader prerequisites', 'Three existing handwritten SDK/Scalar/preimage programs')
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Three independent owned programs under complete421 floor recipe prepared.')
