"""Seal18scoped sources/92audits; preserve every rejected predecessor's zero credit."""
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import tarfile

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
STAGES = [('transfer-concrete-standard-model-20261010-03', 1),
          ('transfer-concrete-standard-model-20261010-08', 2),
          ('transfer-concrete-standard-model-20261010-10', 1),
          ('transfer-concrete-standard-model-20261010-13', 3),
          ('transfer-concrete-standard-model-20261010-18', 1),
          ('transfer-concrete-standard-model-20261010-20', 5),
          ('transfer-concrete-standard-model-20261010-21', 1),
          ('transfer-concrete-standard-model-20261010-22', 3),
          ('transfer-concrete-cofactor-model-20261010-02', 1)]

def pin(path):
    path = Path(path)
    with path.open('rb') as f:
        sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}
entries = []; phases = []
for task_name, count in STAGES:
    task = DIAG / task_name
    plan = json.loads((task / 'plan.json').read_text())
    events = [json.loads(line) for line in (task / 'events.jsonl').read_text().splitlines()]
    completed = [e for e in events if e['event'] == 'attempt_finished']
    passes = [e for e in completed if e['result']['status'] == 'passed']
    assert len(passes) == count
    for e in passes:
        target = next(t for t in plan['targets'] if t['module'] == e['module'])
        result = e['result']
        for r in [target['source'], result['stdout']] + result['objects']:
            assert pin(r['path']) == r
        assert list(result['audits']) == sorted(target['audit_names'])
        assert len(result['audits']) == len(target['audit_names'])
        assert all(set(a['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in result['audits'].values())
        text = Path(result['stdout']['path']).read_bytes().decode('utf-8')
        assert not re.search(r'\b(?:error|warning|info|trace):|\bsorryAx\b', text)
        audits = []
        for name in target['audit_names']:
            pattern = r"(?m)^@?" + re.escape(name) + r"\s*:[\s\S]*?^'" + re.escape(name) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
            matches = list(re.finditer(pattern, text)); assert len(matches) == 1
            signature = matches[0].group(0).split("\n'" + name + "' ", 1)[0]
            assert hashlib.sha256(signature.encode()).hexdigest() == result['audits'][name]['full_type_sha256']
            audits.append({'declaration': name, 'full_type': signature, **result['audits'][name]})
        entries.append({'module': e['module'], 'task': task_name, 'source': target['source'],
                        'audits': audits, 'receipt': result,
                        'source_class': 'generated' if e['module'] in ['EdwardsSecantPolynomials01', 'EdwardsTangentPolynomials01'] else 'handwritten'})
    phases.append({'task': task_name, 'plan': pin(task / 'plan.json'), 'selected_passes': count,
                   'rejected_attempts': [{'module': e['module'], 'reason': e['result']['reason'], 'credit': 0,
                       'semantic_negative_control_credit': 0} for e in completed if e['result']['status'] != 'passed']})
assert len(entries) == 18 and len({e['module'] for e in entries}) == 18
assert sum(len(e['audits']) for e in entries) == 92
packet = ROOT / 'packet'; packet.mkdir(exist_ok=False)
def copy(path, relative):
    path = Path(path); target = packet / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    assert not target.exists()
    shutil.copyfile(path, target)
    assert pin(target)['sha256'] == pin(path)['sha256']
for e in entries:
    copy(e['source']['path'], e['source_class'] + '-source/ShielddSecurity/' + e['module'] + '.lean')
    target = packet / 'proof-audits' / (e['module'] + '.json')
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps({'module': e['module'], 'audits': e['audits'],
                                 'captured_stdout': e['receipt']['stdout'], 'receipt': e['receipt']}, indent=2) + '\n')
for task_name, _ in STAGES:
    task = DIAG / task_name
    for name in ['prepare.py', 'prepare_recipe.py', 'plan.json', 'review.json', 'events.jsonl', 'execute_bounded.py']:
        if (task / name).exists():
            copy(task / name, 'execution-context/' + task_name + '/' + name)
rejected = []
for suffix, reason in [('01', 'Torsion warning rejection'), ('03', 'First-package owned-import admission rejection'),
                      ('05', 'Preparation normalization convention rejected'), ('06', 'Preparation factory assertion rejected'),
                      ('07', 'Origin sequencing warning rejection'), ('08', 'Unused point simplifier warning rejection'),
                      ('10', 'Unused torsion premise/simplifier warning rejection'),
                      ('14', 'Object packaging cap and unused generated binding rejection'),
                      ('16', 'Pre-Lean packaging plan/runner declaration mismatch'),
                      ('18', 'Unreachable handwritten secant tactic rejection'),
                      ('21', 'Unused model classification premise rejection')]:
    task = DIAG / ('transfer-concrete-standard-model-20261010-' + suffix)
    records = []
    for name in ['prepare.py', 'prepare_recipe.py', 'plan.json', 'review.json', 'events.jsonl', 'execute_bounded.py', 'preflight-rejection.json']:
        if (task / name).exists(): records.append(pin(task / name))
    records += [pin(p) for p in (task / 'handwritten').glob('*.lean')]
    records += [pin(p) for p in (task / 'runs').glob('*/stdout.txt')]
    rejected.append({'task': task.name, 'classification': reason, 'immutable_records': records,
                     'rejected_attempt_credit': 0, 'semantic_negative_control_credit': 0})
task = DIAG / 'transfer-concrete-cofactor-model-20261010-01'
records = [pin(task / n) for n in ['prepare.py', 'plan.json', 'review.json', 'events.jsonl', 'execute_bounded.py',
                                  'handwritten/ConcreteCofactorModel01.lean', 'runs/01-ConcreteCofactorModel01/stdout.txt']]
rejected.append({'task': task.name, 'classification': 'Scalar alias rewrite elaboration failure; downstream compiler placeholders rejected',
                 'immutable_records': records, 'rejected_attempt_credit': 0, 'semantic_negative_control_credit': 0})
(packet / 'receipts').mkdir()
(packet / 'receipts/rejected-attempts.json').write_text(json.dumps(rejected, indent=2) + '\n')
(packet / 'receipts/qualified-phases.json').write_text(json.dumps(phases, indent=2) + '\n')
for task_name in ['transfer-concrete-standard-model-20261010-02', 'transfer-concrete-standard-model-20261010-04',
                  'transfer-concrete-standard-model-20261010-09', 'transfer-concrete-standard-model-20261010-11',
                  'transfer-concrete-standard-model-20261010-15', 'transfer-concrete-standard-model-20261010-19']:
    task = DIAG / task_name
    for name in ['prepare.py', 'prepare_recipe.py']:
        if (task / name).exists(): copy(task / name, 'unrun-recipes/' + task_name + '/' + name)
generator = DIAG / 'transfer-edwards-polynomial-generation-20261010-04'
copy(generator / 'generate.py', 'recipes/portable-polynomial-generator/generate.py')
for source in (generator / 'inputs').rglob('*'):
    if source.is_file(): copy(source, 'recipes/portable-polynomial-generator/inputs/' + source.relative_to(generator / 'inputs').as_posix())
for name in ['prepare_recipe.py', 'prepare_portable.py', 'generation-review.json', 'portability-preparation.json']:
    copy(generator / name, 'generation-context/portable/' + name)
gen = DIAG / 'transfer-edwards-polynomial-generation-20261010-02'
for name in ['generate.py', 'prepare_generator.py', 'generation-review.json']:
    copy(gen / name, 'generation-context/qualified/' + name)
def declaration_body(text):
    return '\n'.join(line.rstrip() for line in text.splitlines() if line.strip() and not (
        line.strip() == 'set_option pp.all true in' or line.lstrip().startswith('#check ') or line.lstrip().startswith('#print axioms ')))
reproductions = []
for e in entries:
    if e['source_class'] != 'generated': continue
    original = gen / 'generated' / (e['module'] + '.lean')
    reproduced = generator / 'generated' / original.name
    assert original.read_bytes() == reproduced.read_bytes()
    assert declaration_body(original.read_text()) == declaration_body(Path(e['source']['path']).read_text())
    reproductions.append({'module': e['module'], 'qualified_generated_source': pin(original),
                          'portable_regenerated_source': pin(reproduced), 'compiled_source': e['source'],
                          'declaration_body_sha256': hashlib.sha256(declaration_body(original.read_text()).encode()).hexdigest()})
(packet / 'receipts/generator-reproduction.json').write_text(json.dumps(reproductions, indent=2) + '\n')
pool = DIAG / 'transfer-concrete-cofactor-owned-floor-20261010-02'
for name in ['prepare.py', 'composition-review.json']:
    copy(pool / name, 'owned-import-context/' + name)
check = DIAG / 'transfer-concrete-cofactor-checkpoint-20261010-01'
copy(check / 'preservation.json', 'receipts/preservation.json')
copy(check / 'preservation_check.py', 'recipes/preservation_check.py')
parent = DIAG / 'transfer-closed-cardinality-endpoint-20261010-01'
copy(parent / 'packet/manifest.json', 'inputs/closed-cardinality-parent-manifest.json')
copy(Path(__file__), 'recipes/assemble.py')
files = []
for path in sorted(packet.rglob('*')):
    if path.is_file():
        record = pin(path); record['path'] = path.relative_to(packet).as_posix(); files.append(record)
manifest = {'kind': 'SCOPED_ACTUAL_CONCRETE_ADDITION_MODEL_AND_CLOSED_COFACTOR_JOIN',
    'files': files, 'source_files': 18, 'handwritten_sources': 16, 'generated_sources': 2, 'type_axiom_pairs': 92,
    'modules': [{'module': e['module'], 'source_sha256': e['source']['sha256'], 'audit_pairs': len(e['audits']), 'source_class': e['source_class']} for e in entries],
    'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'closed_cardinality_parent_archive': pin(parent / 'portable-windows-closed-cardinality-endpoint01.tar.xz'),
    'accepted_closed_cardinality_canonical_sha': '5100abd1bc6e9f991f2108d60493906fb14d17b9',
    'latest_parent_canonical_sha_at_seal': 'd733e581da2bd56bbad4ac67e7a937e05250eab6',
    'scope': 'Actual concrete Mathlib Point/Edwards addition compatibility for all cases, complete concrete StandardCurveModel and closed8r cofactor/subgroup/native-constructor mathematical join. Full types expose independent byte-writer/key-subgroup premises.17newly compiled predecessor modules plus one new join; imported old362-point-order proofs and accepted cardinality endpoint are retained, not relabeled freshly replayed.',
    'guard_delta': 'Only artifact64→128MiB/object4→8MiB packaging constants changed from qualified runners. Heap1536MiB/one thread/finite300000heartbeats/rec4096/240s per Lean/600s per task/4GiB Job/pressure/mutex/audit guards unchanged.',
    'open_obligations': ['Pinned SDK SPEND_AUTH equals the traced mathematical base', 'SDK representation and byte/field primitive contract instantiation', 'Whole Transfer row/copy/native correspondence and final portable replay'],
    'runtime_test_credit': 0, 'bounded_model_check_credit': 0, 'semantic_negative_control_credit': 0, 'full_transfer': 'OPEN', 'certification': False,
    'repository_payload_policy': 'Proof sources, generator recipes, normalized full type/axiom evidence and provenance only. Raw compiler logs remain local; no object/toolchain/cache/runtime workspace is included.'}
(packet / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
archive = ROOT / 'portable-windows-concrete-cofactor-endpoint01.tar.xz'
with tarfile.open(archive, 'w:xz', preset=6) as tar:
    for path in sorted(packet.rglob('*')):
        if path.is_file():
            data = path.read_bytes(); info = tarfile.TarInfo(path.relative_to(packet).as_posix())
            info.size = len(data); info.mtime = 0; info.mode = 0o644
            tar.addfile(info, io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 128 * 1024**2
print(json.dumps({'archive': pin(archive), 'manifest': pin(packet / 'manifest.json'),
                  'sources': 18, 'audits': 92, 'full_transfer': 'OPEN', 'certification': False}))
