"""Prepare one actual-curve cofactor join from complete qualified imports."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CLOSED = DIAG / 'transfer-concrete-closed-cardinality-20261010-01'
POOL = DIAG / 'transfer-concrete-cofactor-owned-floor-20261010-02'
def pin(path):
    path = Path(path)
    with path.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}

floor = json.loads((POOL / 'composition-review.json').read_text())
assert floor['admission_ready'] and floor['kernel_credit'] == 0 and floor['objects'] == 401
owned = [r['copy'] for r in floor['selected']]
for r in owned:
    assert pin(r['path']) == r
assert {str(p) for p in (POOL / 'modules/ShielddSecurity').iterdir()} == {r['path'] for r in owned}
source = ROOT / 'handwritten/ConcreteCofactorModel01.lean'
text = source.read_text()
names = ['ShielddSecurity.ConcreteCofactorModel01.' + n for n in re.findall(r'^(?:noncomputable )?(?:theorem|lemma|def) ([A-Za-z0-9_]+)', text, re.M)]
assert len(names) == 8
assert re.findall(r'^#check @([^\n]+)', text, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', text, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', re.sub(r'/--[\s\S]*?-/', '', text))
project = ROOT / 'project/ShielddSecurity'
project.mkdir(parents=True, exist_ok=False)
target = project / source.name
shutil.copyfile(source, target)
runner = ROOT / 'execute_bounded.py'
original = CLOSED / 'execute_bounded.py'
assert pin(original)['sha256'] == '18317ca875ae07d5d79aebe340f7aa13d746b6a55a6b58b53c35ee58c56978db'
runner_text = original.read_text()
assert runner_text.count('ALL_CAP, META_CAP = 64 * 1024**2, 16 * 1024**2') == 1
assert runner_text.count('LOG_CAP, OBJECT_CAP = 1024**2, 4 * 1024**2') == 1
runner_text = runner_text.replace('ALL_CAP, META_CAP = 64 * 1024**2, 16 * 1024**2', 'ALL_CAP, META_CAP = 128 * 1024**2, 16 * 1024**2')
runner_text = runner_text.replace('LOG_CAP, OBJECT_CAP = 1024**2, 4 * 1024**2', 'LOG_CAP, OBJECT_CAP = 1024**2, 8 * 1024**2')
ast.parse(runner_text)
runner.write_text(runner_text, encoding='utf-8', newline='\n')
plan = json.loads((CLOSED / 'plan.json').read_text())
plan['owned_import_pool'] = pin(POOL / 'composition-review.json')
plan['owned_imports'] = owned
plan['lean_path'] = [str(POOL / 'modules'), str(ROOT / 'project')] + plan['lean_path'][2:]
plan['targets'] = [{'module': 'ConcreteCofactorModel01', 'source': pin(target), 'predecessor_source': pin(source),
                    'imports': re.findall(r'^import\s+(\S+)', text, re.M), 'audit_names': names}]
plan['limits']['all_bytes'] = 128 * 1024**2
plan['pins'] += [pin(Path(__file__)), pin(source), pin(target), pin(runner), pin(original),
                 pin(POOL / 'composition-review.json'), pin(POOL / 'prepare.py')]
plan['pins'] += floor['input_records'] + owned
plan['pins'] += [pin(ROOT / 'prepare_recipe.py')] + [pin(DIAG / 'transfer-concrete-cofactor-model-20261010-01' / name) for name in ['prepare.py', 'plan.json', 'execute_bounded.py', 'review.json', 'events.jsonl', 'handwritten/ConcreteCofactorModel01.lean', 'runs/01-ConcreteCofactorModel01/stdout.txt']]
unique = {}
for record in plan['pins']:
    assert record['path'] not in unique or unique[record['path']] == record
    unique[record['path']] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'ACTUAL_CONCRETE_CURVE_MODEL_AND_CLOSED_COFACTOR_JOIN'
plan['scope'] = 'One new handwritten actual Mathlib curve model/global-exponent/cofactor/native-constructor mathematical join, eight full audits. Desired StandardCurveModel/order/cardinality are discharged by qualified concrete proofs. Byte-writer and admitted key subgroup are explicit primitive premises; pinned SDK SPEND_AUTH/representation correspondence and full Transfer remain open.'
plan['source_repairs'] = 'Fresh handwritten scalarModulus/Scalar.order definitional conversion before applying the accepted base-order theorem. No conclusion/premise change, generated edit or new axiom. Preserve the predecessor elaboration rejection, with zero proof/control credit.'
plan['guard_delta'] = {'artifact_cap_bytes': [64*1024**2,128*1024**2], 'object_cap_bytes': [4*1024**2,8*1024**2],
                       'unchanged': 'All heap/RSS/Job/RAM/commit/disk-pressure/single-process/time/heartbeat/recursion/audit/stdout/metadata protections',
                       'scope': 'User-authorized worker packaging judgment under verified disk capacity; physical safeguards unchanged.'}
(ROOT / 'plan.json').write_text(json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n')
review = {'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'owned_objects': len(owned),
          'owned_import_pool': pin(POOL / 'composition-review.json'), 'audits': len(names), 'scope': plan['scope']}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2) + '\n')
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6*8*1024**2 + 1024**2 + 256*1024 < 128*1024**2
print(json.dumps(review))
