"""One immutable plan, two independent named modules, unchanged host guards."""
import hashlib
import json
import re
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-sdk-spend-auth-order-20261010-01'
POOL = DIAG / 'transfer-sdk-native-spend-auth-floor-20261010-02'

def pin(path):
    path = Path(path)
    with path.open('rb') as stream:
        sha = hashlib.file_digest(stream, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}

floor = json.loads((POOL / 'composition-review.json').read_text())
assert floor['admission_ready'] and floor['kernel_credit'] == 0 and floor['objects'] == 427
owned = [record['copy'] for record in floor['selected']]
assert all(pin(r['path']) == r for r in owned)
assert {str(p) for p in (POOL / 'modules/ShielddSecurity').iterdir()} == {r['path'] for r in owned}
records = json.loads((ROOT / 'source-review.json').read_text())
project = ROOT / 'project/ShielddSecurity'
project.mkdir(parents=True, exist_ok=False)
targets = []
inputs = []
for record in records:
    source = Path(record['candidate']['path'])
    assert pin(source) == record['candidate']
    assert pin(record['prior_handwritten']['path']) == record['prior_handwritten']
    text = source.read_text()
    names = record['audit_names']
    assert re.findall(r'^#check @([^\n]+)', text, re.M) == names
    assert re.findall(r'^#print axioms ([^\n]+)', text, re.M) == names
    target = project / source.name
    shutil.copyfile(source, target)
    targets.append({'module': record['module'], 'source': pin(target), 'predecessor_source': pin(source),
                    'imports': re.findall(r'^import ([^\n]+)', text, re.M), 'audit_names': names})
    inputs += [pin(source), pin(target), record['prior_handwritten'], record['predecessor_candidate']]
runner = ROOT / 'execute_bounded.py'
assert pin(PRIOR / 'execute_bounded.py')['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(PRIOR / 'execute_bounded.py', runner)
plan = json.loads((PRIOR / 'plan.json').read_text())
plan['targets'] = targets
plan['pins'] += [pin(ROOT / 'rejected_prepare.py'), pin(ROOT.parent / 'transfer-sdk-raw-route-refresh-20261010-01/prepare.py')]
plan['owned_import_pool'] = pin(POOL / 'composition-review.json')
plan['owned_imports'] = owned
plan['pins'] += floor['input_records'] + owned + [pin(POOL / 'composition-review.json'), pin(POOL / 'prepare.py'), pin(POOL / 'prepare_recipe.py')]
plan['pins'] += inputs + [pin(Path(__file__)), pin(ROOT / 'prepare_fresh.py'), pin(ROOT / 'predecessor_prepare_stage.py'), pin(ROOT / 'source-review.json'), pin(ROOT / 'predecessor_prepare_recipe.py'), pin(runner)]
unique = {}
for record in plan['pins']:
    assert record['path'] not in unique or unique[record['path']] == record
    unique[record['path']] = record
plan['pins'] = list(unique.values())
plan['lean_path'] = [str(POOL / 'modules'), str(ROOT / 'project')] + plan['lean_path'][2:]
plan['pins'] += [pin(ROOT.parent / 'transfer-sdk-raw-point-multiply-20261010-01' / name) for name in ['plan.json','events.jsonl','execute_bounded.py','prepare.py','source-review.json','runs/01-ShielddNativeReadPoint/stdout.txt']]
plan['kind'] = 'OWNED_RAW_POINT_READER_AND_MULTIPLY'
plan['scope'] = 'Two existing handwritten raw coordinate-reader/native-multiply programs with full global contract and program-definition audits. No source correspondence for Rust/FFI primitives or actual circuit rows/copies, no runtime/BMC/control/certification credit.'
plan['source_repairs'] = 'Fresh raw reader replaces only unused case-equation simplifier argument with reflexivity. Multiply body unchanged. Prior strict-warning rejection has zero proof/control/certification credit; finite guards unchanged.'
(ROOT / 'plan.json').write_text(json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n')
review = {'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'owned_objects': 427,
          'owned_import_pool': pin(POOL / 'composition-review.json'), 'sources': 2,
          'audits': sum(len(t['audit_names']) for t in targets), 'scope': plan['scope']}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2) + '\n')
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6*8*1024**2 + 1024**2 + 256*1024 < 128*1024**2
print(json.dumps(review))
