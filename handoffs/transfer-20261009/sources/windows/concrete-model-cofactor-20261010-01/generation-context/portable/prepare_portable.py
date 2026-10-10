"""Package a relocatable deterministic generator; verify unchanged source outputs."""
import ast
import hashlib
import json
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'transfer-edwards-polynomial-generation-20261010-02'
def pin(path):
    path = Path(path)
    with path.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
source = PRIOR / 'generate.py'
assert pin(source)['sha256'] == 'd2c7a9f90dfd8fdf433b33186e9c83716f574c925d131c459507cc89f47492e1'
review = json.loads((PRIOR / 'generation-review.json').read_text())
for r in review['inputs'] + review['generated_sources']:
    assert pin(r['path']) == r
text = source.read_text()
text = text.replace("PUB = Path('C:/src/shieldd-transfer-windows-publication-20261009')\nRECIPES = PUB / 'handoffs/transfer-20261009/sources/windows/standard-curve-model-20261009-01/recipes'", "RECIPES = ROOT / 'inputs/recipes'")
text = text.replace("source = PUB / 'circuits/ShielddSecurity'", "source = ROOT / 'inputs/original-sources'")
text = text.replace("inputs = [pin(ROOT / 'prepare_generator.py'), pin(ROOT.parent / 'transfer-edwards-polynomial-generation-20261010-01/generate.py')]; bodies = {}; derivations = {}", "inputs = []; bodies = {}; derivations = {}")
text = text.replace('import sys\n', 'import sys\nsys.dont_write_bytecode = True\n')
assert 'PUB = Path(' not in text and 'RECIPES = PUB' not in text
ast.parse(text)
(ROOT / 'generate.py').write_text(text, encoding='utf-8', newline='\n')
for r in review['inputs']:
    path = Path(r['path'])
    if path.name.startswith('generate-edwards-'):
        destination = ROOT / 'inputs/recipes' / path.name
    elif path.name.startswith('Edwards') and path.suffix == '.lean':
        destination = ROOT / 'inputs/original-sources' / path.name
    else:
        continue
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(path, destination)
    assert pin(destination)['sha256'] == r['sha256']
(ROOT / 'portability-preparation.json').write_text(json.dumps({
    'recipe': pin(Path(__file__)), 'qualified_proposal_generator': pin(source),
    'prior_generation_review': pin(PRIOR / 'generation-review.json'),
    'portable_generator': pin(ROOT / 'generate.py'), 'kernel_credit': 0,
    'scope': 'Relocatable proposal generator and exact frozen original inputs. Only input/output locations and bytecode-cache policy changed. Await reproduction comparison; no proof/runtime/control/certification credit.'}, indent=2) + '\n')
print('Prepared portable coefficient generator and frozen original inputs.')
