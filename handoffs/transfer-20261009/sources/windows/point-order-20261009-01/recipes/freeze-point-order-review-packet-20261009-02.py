from pathlib import Path
from collections import Counter
import base64, gzip, hashlib, json, re, subprocess

local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
dest = local / 'point-order-review-packet-20261009-02'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
specs = [('point-order', [f'SubgroupPrimeNode{i:02d}' for i in range(1, 38)] + ['SubgroupOrderPrime06', 'ConcretePointOrder01'], None)]

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
    assert m == load(kernel / 'manifest.json') and set(m['order']) == set(expected) and len(m['order']) == len(expected)
    recipe = load(kernel / 'recipe.json')
    assert recipe['memory_MiB'] == 1536 and recipe['finite_seconds_per_module'] == 240 and recipe['threads'] == 1
    guard, auditor = diag / ('root-' + stem + '.ps1'), diag / ('audit-' + stem + '.py')
    assert sha(guard) == recipe['guard_sha256'].lower()
    assert sha(auditor) == recipe['audit_sha256'].lower()
    disk_peak = None
    if prefix == 'point-order':
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


assert len(modules) == 39 and sum(v['audit']['audits'] for v in modules.values()) == 113
assert modules['ConcretePointOrder01']['audit']['audits'] == 1
prime_modules = {n: v for n, v in modules.items() if n != 'ConcretePointOrder01'}
assert len(prime_modules) == 38 and sum(v['audit']['audits'] for v in prime_modules.values()) == 112
for n in prime_modules:
    assert modules[n]['audit']['audits'] == (1 if n == 'SubgroupOrderPrime06' else 3)
plan = local / 'subgroup-prime-platform-replay-plan-20261009-02.json'
assert sha(plan) == '4b8719c29fa524475b9e72f71f847722f144918cac23754e33a2ad98718a7db3'
copy(plan, 'inputs/subgroup-prime-platform-replay-plan-20261009-02.json')
trace_packet = local / 'point-trace-complete-review-packet-20261009-02'
trace_receipt = load(trace_packet / 'receipt.json')
assert trace_receipt['total_qualified_operations'] == 369 and trace_receipt['declaration_audits'] == 3144
write('inherited/complete-point-trace-reference.json', {'packet_directory': str(trace_packet),
      'manifest_sha256': sha(trace_packet / 'manifest.json'), 'receipt_sha256': sha(trace_packet / 'receipt.json'),
      'disposition': 'Previously qualified actual trace/endpoint proof inputs; no repeated credit. Independent review/publication remains separately tracked.'})
for filename in ['prepare-windows-concrete-edwards-universe-types-20261009-01.py',
                 'inspect-field-concrete-closure-20261009-01.py', 'compose-concrete-point-cache-20261009-05.py',
                 'invoke-quiescent-narrow-kernel-20261009-01.ps1', 'record-narrow-execution-context-20261009-01.py',
                 'derive-point-order-preparer-20261009-01.py', 'prepare-point-guarded-disk-scope-20261009-01.py']:
    copy(local / filename, 'recipes/' + filename)
copy(diag / 'native-host-memory-api-01.ps1', 'recipes/native-host-memory-api-01.ps1')
copy(Path(__file__), 'recipes/' + Path(__file__).name)
runtime = Path('C:/src/shieldd-pr160-844389ee')
runtime_sha = '844389ee069e1fb2e576708842d0b389b4d9a44a'
assert subprocess.check_output(['git', '-C', str(runtime), 'rev-parse', 'HEAD'], text=True).strip() == runtime_sha
assert not subprocess.check_output(['git', '-C', str(runtime), 'status', '--porcelain'], text=True).strip()
write('dependency-resolution.json', list(dependencies.values()))
write('receipt.json', {'actual_freeze_checkout_head': subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip(),
      'runtime_sha': runtime_sha, 'mathlib_sha': 'c5ea00351c28e24afc9f0f84379aa41082b1188f', 'lean_version': '4.30.0',
      'fresh_current_host_kernel_modules': 39, 'declaration_audits': 113, 'modules': modules, 'batches': batches,
      'inherited_primality_platform_validation': {'modules': 38, 'declaration_audits': 112,
                                               'theorem_audits': 75, 'definition_audits': 37,
                                               'new_primality_mathematical_results': 0},
      'new_concrete_point_order_root': {'module': 'ConcretePointOrder01', 'theorem': 'ShielddSecurity.ConcretePointOrder01.base_order',
                                        'declaration_audits': 1, 'new_mathematical_results': 1},
      'new_negative_control_credit': 0,
      'proved_scope': ['Exact additive order Scalar.order of the concrete actual Mathlib Point base, consuming certified numerical primality, annihilation and nonidentity'],
      'open': ['independent review/publication of actual order result', 'cardinality', 'native generator correspondence',
               'full Transfer G2-G5/G7 obligations', 'full Transfer'], 'hasse_launch': False,
      'metadata_disposition': 'Inherited numerical primality is not counted again as new mathematics. Exact current-host sources, objects, sidecars, closure/admission/disk receipts and actual execution context are separately checked.'})
write('manifest.json', {'kind': 'Fresh exact concrete-Point-order review packet; no commit or push',
      'files': dict(files), 'review_audit_text_disposition': 'Full successful type/axiom stdout and resources for review; omit raw logs from committed publication', 'full_transfer': 'OPEN'})
payload = json.dumps({'files': {rel: base64.b64encode((dest / rel).read_bytes()).decode() for rel in files}}, separators=(',', ':')).encode()
archive = dest.with_suffix('.json.gz')
assert not archive.exists()
archive.write_bytes(gzip.compress(payload, mtime=0))
print(json.dumps({'marker': 'TRANSFER_POINT_ORDER_REVIEW_PACKET_V1', 'archive': str(archive),
      'sha256': sha(archive), 'bytes': archive.stat().st_size, 'files': len(files),
      'manifest_sha256': sha(dest / 'manifest.json'), 'current_host_kernel_modules': 39,
      'declaration_audits': 113, 'inherited_platform_audits': 112, 'new_point_order_audits': 1, 'full_transfer': 'OPEN'}))
