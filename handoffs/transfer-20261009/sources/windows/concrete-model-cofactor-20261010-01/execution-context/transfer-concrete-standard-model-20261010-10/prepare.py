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
MODULES = ['ConcretePointAdditionPilot01', 'ConcreteTorsionAddition01',
           'EdwardsExceptionalClassification01', 'ConcretePoleAddition01']

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
    original = PUB / (module + '.lean')
    text = original.read_text()
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
ast.parse(runner_text)
runner.write_text(runner_text, encoding='utf-8', newline='\n')
assert pin(runner)['sha256'] == pin(BASE / 'execute_bounded.py')['sha256']
plan['owned_imports'] = owned
plan.pop('owned_import_pool')
plan['lean_path'] = [str(ROOT / 'project')] + plan['lean_path'][2:]
plan['targets'] = targets
records = [pin(Path(__file__)), pin(DIAG / 'transfer-concrete-standard-model-20261010-09/prepare_recipe.py'), pin(ROOT / 'prepare_recipe.py'), pin(DIAG / 'transfer-concrete-standard-model-20261010-05/prepare.py'), pin(DIAG / 'transfer-concrete-standard-model-20261010-06/prepare_recipe.py'), pin(runner), pin(CLOSED / 'plan.json'), pin(POOL / 'composition-review.json'),
           pin(DIAG / 'transfer-base-order-canonical-source-review-20261010-01/review.json'),
           pin(DIAG / 'transfer-base-order-shared-source-review-20261010-02/review.json')]
for task in ['transfer-concrete-standard-model-20261010-01', 'transfer-concrete-standard-model-20261010-03', 'transfer-concrete-standard-model-20261010-07', 'transfer-concrete-standard-model-20261010-08']:
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
plan['scope'] = 'Replay four remaining concrete identity/inverse/torsion/exceptional addition modules; retain the two already qualified origin and Edwards addition modules. Uses exact complete minimum owned import closure in the first PACKAGE root, with the passed nine-audit Torsion module retained. Prior warning failure and pre-Lean import rejection remain zero credit.'
plan['source_repairs'] = 'Remove one observed unused simp argument in mk_neg. No statement/premise/axiom change. Predecessor warning rejection remains zero credit; previously passed modules retain their original receipts.'
plan['repairs'] = 'Return to unchanged qualified standalone own-project runner. All copied owned objects charged here; package root includes the complete exact closure. No runner/resource cap change.'
(ROOT / 'plan.json').write_text(json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n')
review = {'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'owned_objects': len(owned),
          'owned_bytes': sum(r['bytes'] for r in owned), 'targets': MODULES,
          'audits': sum(len(t['audit_names']) for t in targets), 'scope': plan['scope']}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2) + '\n')
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6*4*1024**2 + 1024**2 + 256*1024 < 64*1024**2
print(json.dumps(review))
