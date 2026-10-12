"""Fresh corrected inventory after qualifying the one missing official object."""
import ast
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
EXTRACT = DIAG / 'transfer-cache-lucas-extract-20261010-01'
def pin(p):
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
assert json.loads((EXTRACT / 'result.json').read_text())['status'] == 'passed'
reference = Path('C:/src/shieldd-transfer-windows-publication-20261009/handoffs/transfer-20261009/sources/mac/subgroup-prime06/outputs/mac-subgroup-prime06/official-imports-9b6f311a61ef19f3.json')
expected = json.loads(reference.read_text())['files']
object_root = EXTRACT / 'extracted/.lake/build/lib/lean'
records = []
for suffix in ['.olean', '.olean.private', '.olean.server', '.ilean']:
    p = object_root / ('Mathlib/NumberTheory/LucasPrimality' + suffix)
    r = pin(p)
    assert expected['mathlib/.lake/build/lib/lean/Mathlib/NumberTheory/LucasPrimality' + suffix] == r['sha256']
    records.append(r)
text = (DIAG / 'transfer-external-floor-complete-20261010-05/inventory.py').read_text()
anchor = 'object_root = CACHE'
assert anchor in text
text = text.replace(anchor, anchor + '\n        if module == "Mathlib.NumberTheory.LucasPrimality": object_root = Path(' + repr(str(object_root)) + ')')
ast.parse(text)
(ROOT / 'inventory.py').write_text(text, encoding='utf-8', newline='\n')
(ROOT / 'cache-qualification.json').write_text(json.dumps({'reference': pin(reference), 'extraction_plan': pin(EXTRACT / 'plan.json'), 'extraction_result': pin(EXTRACT / 'result.json'), 'objects': records, 'admission_ready': True, 'scope': 'Exact required object identities and ilean matched published official reference. No semantic correspondence claim or new theorem/runtime/control credit.'}, indent=2) + '\n')
print(json.dumps({'recipe': pin(ROOT / 'inventory.py'), 'qualification': pin(ROOT / 'cache-qualification.json'), 'object_root': str(object_root)}))
