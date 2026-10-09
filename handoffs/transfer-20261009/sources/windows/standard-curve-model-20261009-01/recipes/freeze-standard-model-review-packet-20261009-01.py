from pathlib import Path
import argparse, base64, gzip, hashlib, json, re, subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--pole-run', required=True, choices=['01', '02', '03'])
args = parser.parse_args()
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
dest = local / 'standard-model-review-packet-20261009-01'
assert not dest.exists(), 'fresh frozen review packet required'
dest.mkdir()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
files = {}

def copy(p, rel):
    target = dest / rel
    if rel in files:
        assert sha(p) == files[rel]['sha256']
        return
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(p.read_bytes())
    files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}

def write(rel, value):
    target = dest / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((json.dumps(value, indent=2) + '\n').encode())
    files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}

specs = [
    ('torsion-algebra', '03', 'torsion-algebra', ['EdwardsTorsionAlgebra01']),
    ('point-operation-rows', '03', 'point-operation-rows', ['ConcretePointOperationRows01']),
    ('addition-helpers', '01', 'addition-helpers', ['ConcretePointCoordinates01', 'EdwardsExceptionalClassification01']),
    ('origin-addition', '01', 'origin-addition', ['ConcreteOriginAdditionPilot01']),
    ('torsion-point-transport', '03', 'torsion-point-transport', ['ConcreteTorsionAddition01']),
    ('pole-point-transport', args.pole_run, 'pole-point-transport', ['ConcretePoleAddition01']),
    ('secant-polynomials', '01', 'secant-polynomials', ['EdwardsSecantPolynomials01']),
    ('secant-rational', '02', 'secant-rational', ['EdwardsSecantRational01']),
    ('secant-point-transport', '01', 'secant-point-transport', ['ConcreteSecantAddition01']),
    ('tangent-rational', '01', 'tangent-rational', ['EdwardsTangentPolynomials01','EdwardsTangentRational01']),
    ('tangent-point-transport', '01', 'tangent-point-transport', ['ConcreteTangentAddition01']),
    ('standard-curve-model', '01', 'standard-curve-model', ['ConcreteStandardCurveModel01']),
]
modules, batches, dependencies = {}, {}, {}
tracked = set(subprocess.check_output(['git', '-C', str(repo), 'ls-files'], text=True).splitlines())
for prefix, run, boundary_prefix, expected in specs:
    stem = f'windows-{prefix}-20261009-{run}'
    source, kernel = diag / (stem + '-source'), diag / (stem + '-kernel')
    boundary = diag / f'quiescent-{boundary_prefix}-boundary-20261009{run}'
    for root in [kernel, boundary]:
        assert (root / 'complete.txt').exists() and (root / 'end.txt').exists()
        assert (root / 'exit.txt').read_text().strip() == '0'
    assert (boundary / 'native-resume-disposition.txt').read_text().startswith('not-applicable:')
    m = load(source / 'manifest.json')
    assert m == load(kernel / 'manifest.json')
    assert set(m['order']) == set(expected)
    recipe = load(kernel / 'recipe.json')
    assert recipe['memory_MiB'] == 1536 and recipe['finite_seconds_per_module'] == 240 and recipe['threads'] == 1
    guard = diag / ('root-' + stem + '.ps1')
    auditor = diag / ('audit-' + stem + '.py')
    assert sha(guard) == recipe['guard_sha256'].lower()
    assert sha(auditor) == recipe['audit_sha256'].lower()
    for name in expected:
        leaf = kernel / name
        a = load(leaf / 'audit.json')
        assert a['full_types_checked'] and (leaf / 'exit.txt').read_text().strip() == '0'
        assert (leaf / 'end.txt').exists() and not (leaf / 'stop.txt').exists()
        assert sha(kernel / 'project' / m['sources'][name]['lean_relative_path']) == m['audited_candidates'][name] == a['candidate_sha256']
        original = repo / 'circuits/ShielddSecurity' / (name + '.lean')
        assert sha(original) == m['sources'][name]['sha256'] == a['original_source_sha256']
        output = (leaf / 'stdout.txt').read_text(encoding='utf-8-sig')
        stderr = (leaf / 'stderr.txt').read_text(encoding='utf-8-sig')
        assert not re.search(r'\b(?:error|sorryAx)\b', output + stderr)
        reports = re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", output)
        reports += [(n, '') for n in re.findall(r"'([\w.]+)' does not depend on any axioms", output)]
        assert len(reports) == a['audits'] == len(m['expected_theorems_by_module'][name])
        assert all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in a['axioms'].values())
        for full, used in reports:
            assert set(re.findall(r'[\w.]+', used)) <= {'propext', 'Classical.choice', 'Quot.sound'}
            assert re.search(r'(?:^|\n)@?' + re.escape(full) + r'\s*:', output)
        copy(original, 'maintained-source/' + name + '.lean')
        copy(source / (name + '-audited.lean'), 'audited-source/' + name + '.lean')
        copy(leaf / 'audit.json', 'audits/' + name + '.json')
        copy(leaf / 'stdout.txt', 'review-audit-text/' + name + '.txt')
        modules[name] = {'batch': stem, 'audit': a, 'actual_exit': 0,
            'stdout_sha256': sha(leaf / 'stdout.txt'), 'stderr_sha256': sha(leaf / 'stderr.txt'),
            'start': (leaf / 'start.txt').read_text().strip(), 'end': (leaf / 'end.txt').read_text().strip()}
    for item in m['reused']:
        assert sha(Path(item['original_source'])) == item['original_source_sha256']
        assert sha(Path(item['source'])) == item['source_sha256']
        assert sha(Path(item['object'])) == item['object_sha256']
        for sidecar in item['sidecars']:
            assert sha(Path(sidecar['path'])) == sidecar['sha256']
        key = (item['name'], item['original_source_sha256'])
        candidates = [repo / 'circuits/ShielddSecurity' / Path(item['original_source']).name]
        candidates += list((repo / 'handoffs/transfer-20261009/sources').rglob(Path(item['original_source']).name))
        matches = [p for p in candidates if p.exists() and sha(p) == item['original_source_sha256']]
        assert matches, key
        canonical = matches[0].relative_to(repo).as_posix()
        reference = dict(item, repository_reference=canonical,
            reference_disposition='tracked at actual publication HEAD' if canonical in tracked else 'maintained untracked proof source included in this review packet')
        if canonical not in tracked:
            copy(matches[0], 'maintained-source/' + matches[0].name)
        dependencies.setdefault(key, reference)
        assert dependencies[key]['source_sha256'] == reference['source_sha256']
    for path, digest in m['frozen_import_receipts'].items():
        assert sha(Path(path)) == digest
    for p in [source / 'manifest.json', kernel / 'recipe.json', kernel / 'external-overlay.json', boundary / 'admission.json']:
        copy(p, 'inputs/' + stem + '/' + p.name)
    copy(guard, 'recipes/' + guard.name)
    copy(auditor, 'recipes/' + auditor.name)
    for p in [local / f'compose-{prefix}-cache-20261009-{run}.py', local / f'inspect-{prefix}-closure-20261009-{run}.py']:
        copy(p, 'recipes/' + p.name)
    batches[stem] = {'recipe': recipe, 'scope': m['scope'], 'actual_exit': 0,
        'source_manifest_sha256': sha(source / 'manifest.json'),
        'qualified_external_identities_sha256': sha(kernel / 'qualified-external-identities.json'),
        'external_before_sha256': sha(kernel / 'external-before.json'),
        'start': (kernel / 'start.txt').read_text().strip(), 'end': (kernel / 'end.txt').read_text().strip()}

assert len(modules) == 14 and sum(v['audit']['audits'] for v in modules.values()) == 54
for filename in [
    'prepare-windows-concrete-edwards-20261009-01.py', 'inspect-field-concrete-closure-20261009-01.py',
    'compose-concrete-point-cache-20261009-05.py', 'invoke-quiescent-narrow-kernel-20261009-01.ps1',
    'prepare-torsion-algebra-20261009-03.py', 'prepare-point-operation-rows-20261009-01.py',
    'prepare-point-operation-rows-successor-20261009-03.py', 'prepare-point-operation-rows-20261009-03.py',
    'prepare-addition-helpers-20261009-01.py', 'prepare-addition-helpers-generated-20261009-01.py',
    'prepare-origin-addition-20261009-01.py', 'prepare-origin-addition-generated-20261009-01.py',
    'prepare-torsion-point-transport-20261009-01.py', 'prepare-torsion-point-transport-generated-20261009-01.py',
    'prepare-torsion-point-transport-successor-20261009-02.py', 'prepare-torsion-point-transport-generated-20261009-02.py',
    'prepare-torsion-point-transport-successor-20261009-03.py', 'prepare-torsion-point-transport-generated-20261009-03.py',
    'prepare-pole-point-transport-20261009-01.py', 'prepare-pole-point-transport-generated-20261009-' + args.pole_run + '.py',
]:
    copy(local / filename, 'recipes/' + filename)
copy(diag / 'native-host-memory-api-01.ps1', 'recipes/native-host-memory-api-01.ps1')
copy(Path(__file__), 'recipes/' + Path(__file__).name)
if args.pole_run != '01':
    p = local / ('prepare-pole-point-transport-successor-20261009-' + args.pole_run + '.py')
    copy(p, 'recipes/' + p.name)
for filename in [
    'prepare-secant-polynomials-20261009-01.py','prepare-secant-polynomials-generated-20261009-01.py',
    'prepare-secant-rational-20261009-01.py','prepare-secant-rational-generated-20261009-01.py',
    'prepare-secant-rational-successor-20261009-02.py','prepare-secant-rational-generated-20261009-02.py',
    'prepare-secant-point-transport-20261009-01.py','prepare-secant-point-transport-generated-20261009-01.py',
    'prepare-tangent-rational-20261009-01.py','prepare-tangent-rational-generated-20261009-01.py',
    'prepare-tangent-point-transport-20261009-01.py','prepare-tangent-point-transport-generated-20261009-01.py',
    'prepare-standard-curve-model-20261009-01.py','prepare-standard-curve-model-generated-20261009-01.py',
    'generate-edwards-secant-polynomials-20261009-01.py','generate-edwards-tangent-polynomials-20261009-01.py',
    'prepare-freeze-standard-model-review-packet-20261009-01.py',
]:
    copy(local/filename,'recipes/'+filename)
for filename in ['edwards-secant-polynomial-generation-20261009-01.json','edwards-tangent-polynomial-generation-20261009-01.json']:
    record=load(local/filename)
    module='EdwardsSecantPolynomials01' if 'secant' in filename else 'EdwardsTangentPolynomials01'
    assert record['source_sha256']==modules[module]['audit']['original_source_sha256']
    copy(local/filename,'generation-inputs/'+filename)
write('dependency-resolution.json', list(dependencies.values()))
head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
assert head == '2a12ded169526a215a05e0e25569481fdde0ac97'
receipt = {'actual_publication_checkout_head': head,
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'mathlib_sha': 'c5ea00351c28e24afc9f0f84379aa41082b1188f', 'lean_version': '4.30.0',
    'fresh_modules': 14, 'declaration_audits': 54, 'modules': modules, 'batches': batches,
    'new_negative_control_credit': 0, 'native_resume': 'not applicable: native controller absent',
    'proved_scope': ['torsion rational coordinate identities and same-y classification',
        'actual Mathlib Point secant, tangent and vertical row consumers',
        'coordinates derived from the all-points equivalence', 'Edwards exceptional cross-numerator classification',
        'actual Point origin addition', 'Edwards torsion addition transport for all inputs',
        'Edwards addition transport for every vanishing cross numerator', 'regular secant and tangent polynomial and rational rows', 'regular secant and tangent transport to actual Mathlib Point', 'all-pairs addition compatibility', 'actual Mathlib Point StandardCurveModel with coverage of all Edwards curve solutions'],
    'open': ['scalar trace',
        'point order', 'cardinality', 'native codec', 'other full Transfer G2-G5/G7 obligations', 'full Transfer'],
    'failed_attempts': {'point-operation-rows01': 'compiler failure; batch zero credit',
        'point-operation-rows02-preparation': 'missing inspector path in successor producer; no Lean; zero credit',
        'torsion-point-transport01': 'opaque local binding and helper namespace compiler failures; zero credit',
        'torsion-point-transport02': 'remaining helper namespace compiler failures; zero credit',
        'pole-point-transport01': 'missing denominator unfolding in polynomial proof; batch zero credit', 'secant-rational01': 'No goals to be solved compiler failures in four helper steps; batch zero credit; accidental polynomial replay does not count as new credit'},
    'prior_addition06': {'publication_head': head, 'fresh_modules': 2, 'declaration_audits': 17,
        'receipt': 'handoffs/transfer-20261009/receipts/windows/addition-pilot-20261009-06.json',
        'disposition': 'Published and independently reviewed prior result; not counted as new replay'},
    'inherited_metadata_disposition': 'Prepared manifests retain historical parent metadata; actual HEAD is reported separately. Hashes establish identity, not semantic correspondence.'}
write('receipt.json', receipt)
write('manifest.json', {'kind': 'Frozen local review packet; no commit or push', 'files': dict(files),
    'review_audit_text_disposition': 'Successful full type and axiom text for independent review; omit from committed publication',
    'full_transfer': 'OPEN'})
payload = json.dumps({'files': {rel: base64.b64encode((dest / rel).read_bytes()).decode() for rel in files}}, separators=(',', ':')).encode()
archive = dest.with_suffix('.json.gz')
assert not archive.exists()
archive.write_bytes(gzip.compress(payload, mtime=0))
print(json.dumps({'marker': 'TRANSFER_STANDARD_MODEL_REVIEW_PACKET_V1', 'archive': str(archive),
    'encoding': 'gzip-json-files-base64', 'sha256': sha(archive), 'bytes': archive.stat().st_size,
    'manifest_sha256': sha(dest / 'manifest.json'), 'files': len(files), 'fresh_modules': 14,
    'declaration_audits': 54, 'full_transfer': 'OPEN'}))
