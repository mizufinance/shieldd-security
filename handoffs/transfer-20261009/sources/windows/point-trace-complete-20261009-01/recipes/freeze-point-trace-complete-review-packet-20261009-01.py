from pathlib import Path
from collections import Counter
import base64, gzip, hashlib, json, re, subprocess

local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
dest = local / 'point-trace-complete-review-packet-20261009-01'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
specs = [
    ('point-trace-007-251', [f'ConcretePointTraceStep{i:03d}' for i in range(7, 252)],
     '8e55fc6550ca6ed0f4b7e81fa122f33c25fac4a0'),
    ('point-trace-composition', ['ConcretePointTraceInitial01', 'ConcretePointTraceComposition01'], None)]

# No partial batch may be frozen as a qualified result.
assert not dest.exists()
for prefix, _, _ in specs:
    for root in [diag / f'windows-{prefix}-20261009-01-kernel',
                 diag / f'quiescent-{prefix}-boundary-2026100901']:
        assert (root / 'complete.txt').exists() and (root / 'end.txt').exists()
        assert (root / 'exit.txt').read_text().strip() == '0'
dest.mkdir()
files, modules, batches, dependencies = {}, {}, {}, {}
tracked = set(subprocess.check_output(['git', '-C', str(repo), 'ls-files'], text=True).splitlines())

def copy(p, rel):
    if rel in files:
        assert sha(p) == files[rel]['sha256']
        return
    target = dest / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(p.read_bytes())
    files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}

def write(rel, value):
    target = dest / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((json.dumps(value, indent=2) + '\n').encode())
    files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}

for prefix, expected, execution_head in specs:
    stem = f'windows-{prefix}-20261009-01'
    kernel, source = diag / (stem + '-kernel'), diag / (stem + '-source')
    boundary = diag / f'quiescent-{prefix}-boundary-2026100901'
    m = load(source / 'manifest.json')
    assert m == load(kernel / 'manifest.json') and m['order'] == expected
    recipe = load(kernel / 'recipe.json')
    assert recipe['memory_MiB'] == 1536 and recipe['finite_seconds_per_module'] == 240 and recipe['threads'] == 1
    guard, auditor = diag / ('root-' + stem + '.ps1'), diag / ('audit-' + stem + '.py')
    assert sha(guard) == recipe['guard_sha256'].lower()
    assert sha(auditor) == recipe['audit_sha256'].lower()
    disk_peak = None
    if prefix == 'point-trace-composition':
        disk_samples = kernel / 'scoped-artifact-disk-samples.txt'
        sizes = [int(float(line.split()[-1])) for line in disk_samples.read_text(encoding='utf-8-sig').splitlines() if line.strip()]
        assert sizes and max(sizes) <= 2147483648
        disk_peak = max(sizes)
        copy(disk_samples, 'resource-samples/' + prefix + '-scoped-artifact-disk.txt')
    if execution_head is None:
        context_path = local / f'{prefix}-execution-context-20261009-01.json'
        context = load(context_path)
        assert context['batch'] == stem and context['guard_sha256'] == sha(guard)
        assert context['source_manifest_sha256'] == sha(source / 'manifest.json')
        execution_head = context['actual_execution_checkout_head']
        copy(context_path, 'inputs/' + stem + '/execution-context.json')
    for name in expected:
        leaf = kernel / name
        a = load(leaf / 'audit.json')
        assert a['full_types_checked'] and (leaf / 'exit.txt').read_text().strip() == '0'
        assert (leaf / 'end.txt').exists() and not (leaf / 'stop.txt').exists()
        original = repo / 'circuits/ShielddSecurity' / (name + '.lean')
        assert sha(original) == m['sources'][name]['sha256'] == a['original_source_sha256']
        assert sha(kernel / 'project' / m['sources'][name]['lean_relative_path']) == m['audited_candidates'][name] == a['candidate_sha256']
        stdout, stderr = leaf / 'stdout.txt', leaf / 'stderr.txt'
        output = stdout.read_text(encoding='utf-8-sig')
        assert not re.search(r'\b(?:error|sorryAx)\b', output + stderr.read_text(encoding='utf-8-sig'))
        reports = re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", output)
        reports += [(n, '') for n in re.findall(r"'([\w.]+)' does not depend on any axioms", output)]
        assert len(reports) == a['audits'] == len(m['expected_theorems_by_module'][name])
        assert all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in a['axioms'].values())
        for full, used in reports:
            assert set(re.findall(r'[\w.]+', used)) <= {'propext', 'Classical.choice', 'Quot.sound'}
            assert re.search(r'(?:^|\n)@?' + re.escape(full) + r'(?:\.\{[^}\n]+\})?\s*:', output)
        copy(original, 'maintained-source/' + name + '.lean')
        copy(source / (name + '-audited.lean'), 'audited-source/' + name + '.lean')
        copy(leaf / 'audit.json', 'audits/' + name + '.json')
        copy(stdout, 'review-audit-text/' + name + '.txt')
        copy(leaf / 'memory.txt', 'resource-samples/' + name + '.txt')
        modules[name] = {'batch': stem, 'audit': a, 'actual_exit': 0,
                         'stdout_sha256': sha(stdout), 'stderr_sha256': sha(stderr),
                         'start': (leaf / 'start.txt').read_text().strip(),
                         'end': (leaf / 'end.txt').read_text().strip()}
    for item in m['reused']:
        for path, digest in [(item['original_source'], item['original_source_sha256']),
                             (item['source'], item['source_sha256']), (item['object'], item['object_sha256'])]:
            assert sha(Path(path)) == digest
        for extra in item['sidecars']:
            assert sha(Path(extra['path'])) == extra['sha256']
        candidates = [repo / 'circuits/ShielddSecurity' / Path(item['original_source']).name]
        candidates += list((repo / 'handoffs/transfer-20261009/sources').rglob(Path(item['original_source']).name))
        matches = [p for p in candidates if p.exists() and sha(p) == item['original_source_sha256']]
        assert matches, item['name']
        canonical = matches[0].relative_to(repo).as_posix()
        reference = dict(item, repository_reference=canonical,
                         reference_disposition='tracked at freeze HEAD' if canonical in tracked else 'fresh maintained source included in this packet')
        if canonical not in tracked:
            copy(matches[0], 'maintained-source/' + matches[0].name)
        key = (item['name'], item['original_source_sha256'])
        dependencies.setdefault(key, reference)
        assert dependencies[key]['source_sha256'] == reference['source_sha256']
    for path, digest in m['frozen_import_receipts'].items():
        assert sha(Path(path)) == digest
    for p in [source / 'manifest.json', kernel / 'recipe.json', kernel / 'external-overlay.json']:
        copy(p, 'inputs/' + stem + '/' + p.name)
    for name in ['admission.json', 'native-resume-disposition.txt', 'start.txt', 'end.txt', 'complete.txt', 'exit.txt']:
        copy(boundary / name, 'boundary/' + prefix + '/' + name)
    assert (boundary / 'native-resume-disposition.txt').read_text().startswith('not-applicable:')
    for p in [guard, auditor, local / f'prepare-{prefix}-20261009-01.py',
              local / f'compose-{prefix}-cache-20261009-01.py', local / f'inspect-{prefix}-closure-20261009-01.py']:
        copy(p, 'recipes/' + p.name)
    batches[stem] = {'recipe': recipe, 'scope': m['scope'], 'actual_exit': 0,
                    'scoped_artifact_disk_peak_bytes': disk_peak,
                    'actual_execution_checkout_head': execution_head,
                    'source_manifest_sha256': sha(source / 'manifest.json'),
                    'qualified_external_identities_sha256': sha(kernel / 'qualified-external-identities.json'),
                    'external_before_sha256': sha(kernel / 'external-before.json'),
                    'start': (kernel / 'start.txt').read_text().strip(), 'end': (kernel / 'end.txt').read_text().strip()}

assert len(modules) == 247 and sum(v['audit']['audits'] for v in modules.values()) == 3144
candidate = repo / 'handoffs/transfer-20261009/sources/parent/weierstrass-order-inputs01/candidate.json'
assert sha(candidate) == '028924209b34a15720e93083253a54b4fe2f759bd19e93e43fdf2707c576096c'
data = load(candidate)
record = local / 'point-trace-generation-20261009-01-007-251.json'
proposal = load(record)
assert proposal['candidate_sha256'] == sha(candidate)
assert proposal['producer_sha256'] == sha(local / 'generate-concrete-point-trace-20261009-01.py')
assert len(proposal['steps']) == 245 and sum(len(s['operation_cases']) for s in proposal['steps']) == 357
for step in proposal['steps']:
    assert step['source_sha256'] == modules[step['module']]['audit']['original_source_sha256']
copy(record, 'generation-inputs/' + record.name)
portable_data = local / 'point-trace-portable-byte-replay-data-20261009-01.json'
replay = load(portable_data)
assert replay['modules_byte_exact'] == 249 and replay['new_kernel_credit'] == 0
assert replay['producer_sha256'] == sha(local / 'generate-concrete-point-trace-portable-20261009-01.py')
assert replay['verifier_sha256'] == sha(local / 'verify-point-trace-portable-byte-replay-20261009-01.py')
assert replay['candidate_sha256'] == sha(candidate)
assert replay['scalar_source_sha256'] == sha(repo / 'circuits/ShielddSecurity/Scalar.lean')
assert all(replay['independently_checked_final_branch_data'].values())
for name, identity in replay['source_identities'].items():
    assert sha(repo / 'circuits/ShielddSecurity' / name) == identity['sha256']
copy(portable_data, 'generation-inputs/' + portable_data.name)
write('generation-inputs/candidate-reference.json', {'repository_reference': candidate.relative_to(repo).as_posix(),
      'sha256': sha(candidate), 'bytes': candidate.stat().st_size, 'runtime_sha': data['runtime_sha'],
      'disposition': 'Exact published canonical input, not duplicated'})

census = []
for index, step in enumerate(data['steps']):
    assert step['prefix'] == (1 if index == 0 else data['steps'][index-1]['prefix'] * 2 + step['bit'])
    for slot in ['doubling', 'addition']:
        row = step[slot]
        if row is None:
            continue
        if index == 0:
            module, theorem, stem = 'ConcretePointTraceInitial01', ('initial_double' if slot == 'doubling' else 'initial_add'), 'windows-point-trace-composition-20261009-01'
        elif index == 1:
            module, theorem, stem = 'ConcretePointOperationPilot01', ('first_double' if slot == 'doubling' else 'first_add'), 'windows-point-operation-pilot-20261009-01'
        elif index == 2:
            module, theorem, stem = 'ConcretePointOperationPilot02', ('next_double' if slot == 'doubling' else 'next_add'), 'windows-point-operation-pilot-20261009-04'
        else:
            module = f'ConcretePointTraceStep{index:03d}'
            theorem = 'next_double' if slot == 'doubling' else ('final_add' if row['case'] == 'inverse' else 'next_add')
            stem = 'windows-point-trace-003-006-20261009-01' if index <= 6 else 'windows-point-trace-007-251-20261009-01'
        kernel = diag / (stem + '-kernel')
        assert (kernel / 'complete.txt').exists() and (kernel / 'exit.txt').read_text().strip() == '0'
        a = load(kernel / module / 'audit.json')
        full = f'ShielddSecurity.{module}.{theorem}'
        assert a['full_types_checked'] and full in a['axioms']
        census.append({'candidate_step_index': index, 'slot': slot, 'case': row['case'], 'module': module,
                       'theorem': full, 'source_sha256': a['original_source_sha256'],
                       'audited_source_sha256': a['candidate_sha256'], 'batch': stem,
                       'kernel_type_axiom_qualified': True,
                       'parent_review_status': 'pending' if module in modules else 'published independently reviewed prior result'})
assert len(census) == 369 and Counter(x['case'] for x in census) == Counter(double=251, add=115, inverse=1, left_infinity=2)
write('operation-coverage-census.json', {'candidate_sha256': sha(candidate), 'operations': census,
      'total': 369, 'qualified_operations': 369, 'new_operations': 359, 'prior_published_operations': 10,
      'association_classification': 'DATA/identity association of candidate index, slot and case to separately kernel-proved Point statements; no standalone chain graph-link theorem',
      'scope': 'Actual Point binary scalar trace; native generator correspondence OPEN', 'full_transfer': 'OPEN'})

runtime = Path('C:/src/shieldd-pr160-844389ee')
assert subprocess.check_output(['git', '-C', str(runtime), 'rev-parse', 'HEAD'], text=True).strip() == data['runtime_sha']
assert not subprocess.check_output(['git', '-C', str(runtime), 'status', '--porcelain'], text=True).strip()
for filename in ['prepare-windows-concrete-edwards-universe-types-20261009-01.py',
                 'inspect-field-concrete-closure-20261009-01.py', 'compose-concrete-point-cache-20261009-05.py',
                 'invoke-quiescent-narrow-kernel-20261009-01.ps1', 'generate-concrete-point-trace-20261009-01.py',
                 'derive-point-trace-composition-preparer-20261009-01.py', 'record-narrow-execution-context-20261009-01.py',
                 'derive-portable-point-trace-generator-20261009-01.py', 'generate-concrete-point-trace-portable-20261009-01.py',
                 'verify-point-trace-portable-byte-replay-20261009-01.py', 'prepare-point-guarded-disk-scope-20261009-01.py']:
    copy(local / filename, 'recipes/' + filename)
copy(diag / 'native-host-memory-api-01.ps1', 'recipes/native-host-memory-api-01.ps1')
copy(Path(__file__), 'recipes/' + Path(__file__).name)
write('dependency-resolution.json', list(dependencies.values()))
head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
write('receipt.json', {'actual_freeze_checkout_head': head, 'runtime_sha': data['runtime_sha'],
      'mathlib_sha': 'c5ea00351c28e24afc9f0f84379aa41082b1188f', 'lean_version': '4.30.0',
      'fresh_modules': 247, 'declaration_audits': 3144, 'modules': modules, 'batches': batches,
      'new_operations': 359, 'prior_published_operations': 10, 'total_qualified_operations': 369,
      'new_negative_control_credit': 0,
      'proved_scope': ['initial identity operations and one-scalar prefix on the same concrete actual Mathlib Point base',
                       'actual Point operation witnesses and symbolic scalar prefix equalities in each qualified named trace module',
                       'exact Scalar.order annihilation, concrete base nonidentity and initial/final endpoint conjunction'],
      'candidate_association_scope': 'The 369-operation census checks exact scalar/base/candidate association as DATA; initial facts are not a separate chain graph-link theorem',
      'open': ['independent review/publication of fresh trace', 'exact point order', 'cardinality',
               'native generator correspondence', 'full Transfer G2-G5/G7 obligations', 'full Transfer'],
      'metadata_disposition': 'Prepared historical metadata retained; actual execution heads reported separately. Hashes establish identity, not semantic correspondence.'})
write('manifest.json', {'kind': 'Fresh exact complete-Point-trace review packet; no commit or push',
      'files': dict(files), 'review_audit_text_disposition': 'Full successful type/axiom stdout for independent review; omit from committed publication', 'full_transfer': 'OPEN'})
payload = json.dumps({'files': {rel: base64.b64encode((dest / rel).read_bytes()).decode() for rel in files}}, separators=(',', ':')).encode()
archive = dest.with_suffix('.json.gz')
assert not archive.exists()
archive.write_bytes(gzip.compress(payload, mtime=0))
print(json.dumps({'marker': 'TRANSFER_POINT_TRACE_COMPLETE_REVIEW_PACKET_V1', 'archive': str(archive),
      'sha256': sha(archive), 'bytes': archive.stat().st_size, 'files': len(files),
      'manifest_sha256': sha(dest / 'manifest.json'), 'fresh_modules': 247, 'declaration_audits': 3144,
      'qualified_operations': 369, 'full_transfer': 'OPEN'}))
