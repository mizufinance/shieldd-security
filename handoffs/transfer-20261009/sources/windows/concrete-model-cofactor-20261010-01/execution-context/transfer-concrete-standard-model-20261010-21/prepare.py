"""Use the minimum complete owned package closure; retain every rejected attempt."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PUB = Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity')
CLOSED = DIAG / 'transfer-concrete-closed-cardinality-20261010-01'
PRIOR = DIAG / 'transfer-concrete-standard-model-20261010-03'
BASE = DIAG / 'transfer-concrete-cardinality-join-20261010-01'
POOL = DIAG / 'transfer-base-order-owned-floor-20261010-02'
MODULES = ['ConcretePointCoordinates01', 'ConcreteStandardCurveModel01',
           'GroupNativeAuthorization', 'GroupNativeCofactor']

def pin(path):
    path = Path(path)
    with path.open('rb') as f:
        digest = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': digest}

def body(text):
    return '\n'.join(line.rstrip() for line in text.splitlines() if line.strip() and not (
        line.strip() == 'set_option pp.all true in' or line.lstrip().startswith('#check ') or
        line.lstrip().startswith('#print axioms ')))

plan = json.loads((CLOSED / 'plan.json').read_text())
floor = json.loads((POOL / 'composition-review.json').read_text())
assert floor['admission_ready'] and floor['kernel_credit'] == 0
selected = {Path(r['copy']['path']).stem: r['copy'] for r in floor['selected']}
canonical = json.loads((DIAG / 'transfer-base-order-canonical-source-review-20261010-01/review.json').read_text())
shared = json.loads((DIAG / 'transfer-base-order-shared-source-review-20261010-02/review.json').read_text())
assert canonical['all_match'] and shared['all_same_declaration_source_body']
canonical_by_name = {r['module'].split('.', 1)[1]: r for r in canonical['modules']}
shared_by_name = {r['module'].split('.', 1)[1]: r for r in shared['modules']}
needed = set()
source_pins = []
def visit(module):
    if module in needed:
        return
    needed.add(module)
    source = PUB / (module + '.lean')
    assert source.is_file()
    source_pins.append(pin(source))
    if module in selected:
        original = canonical_by_name[module]
        assert pin(source) == original['canonical_source']
        assert hashlib.sha256(body(source.read_text()).encode()).hexdigest() == original['declaration_body_sha256']
        if module in shared_by_name:
            current = shared_by_name[module]
            assert selected[module]['bytes'] == current['current_object']['bytes']
            assert selected[module]['sha256'] == current['current_object']['sha256']
        else:
            assert selected[module]['bytes'] == original['compiled_object']['bytes']
            assert selected[module]['sha256'] == original['compiled_object']['sha256']
    for imported in re.findall(r'^import\s+ShielddSecurity\.(\S+)', source.read_text(), re.M):
        visit(imported)
visit('ConcreteStandardCurveModel01')
visit('GroupNativeCofactor')
originals = [selected[name] for name in sorted(needed & set(selected))]
events = [json.loads(line) for line in (PRIOR / 'events.jsonl').read_text().splitlines()]
passed = [e for e in events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']
assert len(passed) == 1 and passed[0]['module'] == 'EdwardsTorsionAlgebra01'
assert events[-1]['result']['status'] == 'failed'
originals += passed[0]['result']['objects']
NEXT = DIAG / 'transfer-concrete-standard-model-20261010-08'
next_events = [json.loads(line) for line in (NEXT / 'events.jsonl').read_text().splitlines()]
next_passed = [e for e in next_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']
assert len(next_passed) == 2 and next_events[-1]['result']['status'] == 'failed'
originals += [p for e in next_passed for p in e['result']['objects']]
LAST = DIAG / 'transfer-concrete-standard-model-20261010-10'
last_events = [json.loads(line) for line in (LAST / 'events.jsonl').read_text().splitlines()]
last_passed = [e for e in last_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']
assert len(last_passed) == 1 and last_events[-1]['result']['status'] == 'failed'
originals += [p for e in last_passed for p in e['result']['objects']]
FINAL = DIAG / 'transfer-concrete-standard-model-20261010-13'
final_events = [json.loads(line) for line in (FINAL / 'events.jsonl').read_text().splitlines()]
final_passed = [e for e in final_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']
assert len(final_passed) == 3 and final_events[-1]['result']['status'] == 'passed'
originals += [p for e in final_passed for p in e['result']['objects']]
SECANT = DIAG / 'transfer-concrete-standard-model-20261010-18'
secant_events = [json.loads(line) for line in (SECANT / 'events.jsonl').read_text().splitlines()]
secant_passed = [e for e in secant_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']
assert len(secant_passed) == 1 and secant_events[-1]['result']['status'] == 'failed'
originals += [p for e in secant_passed for p in e['result']['objects']]
TANGENT = DIAG / 'transfer-concrete-standard-model-20261010-20'
tangent_events = [json.loads(line) for line in (TANGENT / 'events.jsonl').read_text().splitlines()]
tangent_passed = [e for e in tangent_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']
assert len(tangent_passed) == 5 and tangent_events[-1]['result']['status'] == 'passed'
originals += [p for e in tangent_passed for p in e['result']['objects']]
project = ROOT / 'project/ShielddSecurity'
project.mkdir(parents=True, exist_ok=False)
handwritten = ROOT / 'handwritten'
handwritten.mkdir(exist_ok=False)
owned = []
for original in originals:
    assert pin(original['path']) == original
    target = project / Path(original['path']).name
    shutil.copyfile(original['path'], target)
    owned.append(pin(target))
targets = []
for module in MODULES:
    GEN = DIAG / 'transfer-edwards-polynomial-generation-20261010-02'
    original = (GEN / 'generated' if module in ['EdwardsSecantPolynomials01', 'EdwardsTangentPolynomials01'] else PUB) / (module + '.lean')
    text = original.read_text()
    if module == 'EdwardsSecantRational01':
        assert text.count('field_simp [nonzeroD] <;> ring') == 4
        text = text.replace('field_simp [nonzeroD] <;> ring', 'field_simp [nonzeroD]')
    if module == 'ConcreteTorsionAddition01':
        assert text.count('variable [DecidableEq F]\n\n') == 1
        text = text.replace('variable [DecidableEq F]\n\n', '')
        text = text.replace('theorem regular_equivalence ', 'variable [DecidableEq F]\n\ntheorem regular_equivalence ')
        needle = 'simp only [WeierstrassCurve.Affine.Point.some.injEq, xValue, yValue, and_self]'
        assert text.count(needle) == 1
        text = text.replace(needle, 'simp only [xValue, yValue]')
    if module == 'ConcretePointAdditionPilot01':
        needle = 'simp [WeierstrassCurve.Affine.Point.some.injEq,\n    WeierstrassCurve.Affine.negY, curve]'
        assert text.count(needle) == 1
        text = text.replace(needle, 'simp [WeierstrassCurve.Affine.negY, curve]')
    if module == 'ConcreteOriginAdditionPilot01':
        assert text.count('field_simp [nonzeroX] <;> ring') == 2
        text = text.replace('field_simp [nonzeroX] <;> ring', 'field_simp [nonzeroX]; ring')
    namespace = re.findall(r'^namespace (\S+)', text, re.M)
    assert len(namespace) == 1
    names = [namespace[0] + '.' + name for name in re.findall(
        r'^(?:noncomputable )?(?:theorem|lemma|def) ([A-Za-z0-9_]+)', text, re.M)]
    assert names
    text = '\n'.join(line for line in text.splitlines() if not (
        line.strip() == 'set_option pp.all true in' or line.lstrip().startswith('#check ') or
        line.lstrip().startswith('#print axioms '))) + '\n'
    for name in names:
        text += '\nset_option pp.all true in\n#check @' + name + '\n#print axioms ' + name + '\n'
    source = handwritten / original.name
    source.write_text(text, encoding='utf-8', newline='\n')
    target = project / original.name
    shutil.copyfile(source, target)
    source_pins += [pin(source), pin(target)]
    targets.append({'module': module, 'source': pin(target), 'predecessor_source': pin(source),
                    'imports': re.findall(r'^import\s+(\S+)', text, re.M), 'audit_names': names})
runner = ROOT / 'execute_bounded.py'
runner_text = (BASE / 'execute_bounded.py').read_text()
assert pin(BASE / 'execute_bounded.py')['sha256'] == '0e3bd581f2724e468153228c8b0be62996b4e3bc74008db36a89b3cd248b8861'
assert runner_text.count('ALL_CAP, META_CAP = 64 * 1024**2, 16 * 1024**2') == 1
assert runner_text.count('LOG_CAP, OBJECT_CAP = 1024**2, 4 * 1024**2') == 1
runner_text = runner_text.replace('ALL_CAP, META_CAP = 64 * 1024**2, 16 * 1024**2', 'ALL_CAP, META_CAP = 128 * 1024**2, 16 * 1024**2')
runner_text = runner_text.replace('LOG_CAP, OBJECT_CAP = 1024**2, 4 * 1024**2', 'LOG_CAP, OBJECT_CAP = 1024**2, 8 * 1024**2')
ast.parse(runner_text)
runner.write_text(runner_text, encoding='utf-8', newline='\n')
assert pin(runner)['sha256'] != pin(BASE / 'execute_bounded.py')['sha256']
plan['owned_imports'] = owned
plan['limits']['all_bytes'] = 128 * 1024**2
plan.pop('owned_import_pool')
plan['lean_path'] = [str(ROOT / 'project')] + plan['lean_path'][2:]
plan['targets'] = targets
records = [pin(Path(__file__))] + [pin(DIAG / 'transfer-concrete-standard-model-20261010-16' / name) for name in ['plan.json', 'prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'review.json', 'preflight-rejection.json']] + [ pin(DIAG / 'transfer-edwards-polynomial-generation-20261010-02/generate.py'), pin(DIAG / 'transfer-edwards-polynomial-generation-20261010-02/prepare_generator.py'), pin(DIAG / 'transfer-edwards-polynomial-generation-20261010-02/generation-review.json'), pin(DIAG / 'transfer-concrete-standard-model-20261010-15/prepare_recipe.py'), pin(DIAG / 'transfer-concrete-standard-model-20261010-13/prepare.py'), pin(DIAG / 'transfer-concrete-standard-model-20261010-11/prepare_recipe.py'), pin(DIAG / 'transfer-concrete-standard-model-20261010-09/prepare_recipe.py'), pin(ROOT / 'prepare_recipe.py'), pin(DIAG / 'transfer-concrete-standard-model-20261010-05/prepare.py'), pin(DIAG / 'transfer-concrete-standard-model-20261010-06/prepare_recipe.py'), pin(runner), pin(CLOSED / 'plan.json'), pin(POOL / 'composition-review.json'),
           pin(DIAG / 'transfer-base-order-canonical-source-review-20261010-01/review.json'),
           pin(DIAG / 'transfer-base-order-shared-source-review-20261010-02/review.json')]
for task in ['transfer-concrete-standard-model-20261010-01', 'transfer-concrete-standard-model-20261010-03', 'transfer-concrete-standard-model-20261010-07', 'transfer-concrete-standard-model-20261010-08', 'transfer-concrete-standard-model-20261010-10', 'transfer-concrete-standard-model-20261010-13', 'transfer-concrete-standard-model-20261010-14', 'transfer-concrete-standard-model-20261010-18', 'transfer-concrete-standard-model-20261010-20']:
    root = DIAG / task
    records += [pin(root / name) for name in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'prepare.py', 'review.json']]
    records += [pin(p) for p in (root / 'handwritten').glob('*.lean')]
    records += [pin(p) for p in (root / 'runs').glob('*/stdout.txt')]
plan['pins'] += records + source_pins + originals + owned
unique = {}
for record in plan['pins']:
    assert record['path'] not in unique or unique[record['path']] == record
    unique[record['path']] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'MINIMUM_COMPLETE_OWNED_ADDITION_MODEL_REPLAY'
plan['scope'] = 'Replay concrete coordinates, complete StandardCurveModel and native authorization/cofactor mathematical contracts from qualified complete addition proofs. SDK representation and full Transfer correspondence remain open. Uses exact complete minimum owned import closure in the first PACKAGE root, with the passed nine-audit Torsion module retained. Prior warning failure and pre-Lean import rejection remain zero credit.'
plan['source_repairs'] = 'These four maintained declaration/proof bodies are unchanged; complete ordered type/axiom audits are appended. Regenerated polynomial imports retain their qualified receipts.'
plan['guard_delta'] = {'artifact_cap_bytes': [64*1024**2,128*1024**2], 'object_cap_bytes': [4*1024**2,8*1024**2], 'unchanged': 'All heap/RSS/Job/RAM/commit/disk-pressure/single-process/time/heartbeat/recursion/audit/stdout/metadata protections', 'disk_free_bytes_at_review': 82500661248, 'authorization_context': 'User autonomy clarification: crash prevention is the limiting concern; safe artifact packaging thresholds may be chosen with verified disk capacity.'}
plan['repairs'] = 'Standalone bounded runner changes only two non-memory constants: artifact128MiB/object8MiB. All physical memory and correctness safeguards remain byte-identical. All copied owned objects remain charged; first package contains the complete closure.'
(ROOT / 'plan.json').write_text(json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n')
review = {'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'owned_objects': len(owned),
          'owned_bytes': sum(r['bytes'] for r in owned), 'targets': MODULES,
          'audits': sum(len(t['audit_names']) for t in targets), 'scope': plan['scope']}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2) + '\n')
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6*8*1024**2 + 1024**2 + 256*1024 < 128*1024**2
print(json.dumps(review))
