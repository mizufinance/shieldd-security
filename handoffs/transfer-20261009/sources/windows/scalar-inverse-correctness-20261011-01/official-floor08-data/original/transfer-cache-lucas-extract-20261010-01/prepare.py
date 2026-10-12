"""Extract exactly one existing official archive into a fresh guarded root."""
import ast
import hashlib
import json
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
LOOKUP = DIAG / 'transfer-cache-lucas-lookup-20261010-01'
OLD_EXTRACT = DIAG / 'transfer-cache-extract78-20261010-05'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
lookup = json.loads((LOOKUP / 'plan.json').read_text())
result = json.loads((LOOKUP / 'result.json').read_text())
assert result['status'] == 'passed' and result['stdout_sha256'] == pin(LOOKUP / 'stdout.txt')['sha256']
pairs = dict(re.findall(r'^([A-Za-z0-9_.]+): (.+\.ltar)$', (LOOKUP / 'stdout.txt').read_text(), re.M))
assert set(pairs) == {'Mathlib.NumberTheory.LucasPrimality'}
archive = pin(pairs['Mathlib.NumberTheory.LucasPrimality'])
text = (OLD_EXTRACT / 'execute_metadata.py').read_text().replace("assert len(plan['modules']) == 39", "assert plan['modules'] == ['Mathlib.NumberTheory.LucasPrimality']")
ast.parse(text)
(ROOT / 'execute_metadata.py').write_text(text, encoding='utf-8', newline='\n')
(ROOT / 'extracted').mkdir(exist_ok=False)
exe = Path(lookup['toolchain_bin']) / 'leantar.exe'
plan = {**lookup, 'kind': 'ONE_EXISTING_OFFICIAL_CACHE_EXTRACTION', 'archives': [archive], 'cwd': str(ROOT),
    'command': [str(exe), '--jobs', '1', '-x', '-C', str(ROOT / 'extracted'), archive['path']],
    'pins': lookup['pins'] + [archive, pin(exe), pin(ROOT / 'execute_metadata.py'), pin(Path(__file__)), pin(LOOKUP / 'plan.json'), pin(LOOKUP / 'result.json'), pin(LOOKUP / 'stdout.txt'), pin(OLD_EXTRACT / 'execute_metadata.py')],
    'scope': 'One cached archive extracted within fresh scratch root with unchanged finite metadata guards. Existing archive/source remain read-only. No proof, compilation, download, native or semantic control credit.'}
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'archive': archive}))
