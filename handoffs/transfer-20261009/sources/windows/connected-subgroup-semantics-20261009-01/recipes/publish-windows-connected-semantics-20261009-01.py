from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys
repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
base = repo / 'handoffs/transfer-20261009'
dest = base / 'sources/windows/connected-subgroup-semantics-20261009-01'
checks = {'template': ('windows-subgroup-source-graph-20261009-05', 'safe-subgroup-source-graph-boundary-2026100905', 'GroupSubgroupSourceGraph'),
          'concrete': ('windows-connected-subgroup-semantics-20261009-01', 'safe-connected-subgroup-semantics-boundary-2026100901', 'TransferFirstSubgroupSemantics01')}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
write = lambda p, v: p.write_bytes((json.dumps(v, indent=2) + '\n').encode())
for stem, boundary, root in checks.values():
    kernel = diag / (stem + '-kernel')
    assert (kernel / 'complete.txt').exists() and (kernel / 'end.txt').exists()
    assert (kernel / 'exit.txt').read_text().strip() == '0'
    assert (diag / boundary / 'exit.txt').read_text().strip() == '0'
    assert (diag / boundary / 'resume-status.txt').read_text().strip() == '0'
phase = sys.argv[1]
if phase == 'sources':
    assert not dest.exists()
    dest.mkdir(parents=True)
    files = {}
    def copy(source, rel):
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(source.read_bytes())
        assert sha(target) == sha(source)
        files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}
    for label, (stem, boundary, root) in checks.items():
        prepared = diag / (stem + '-source')
        copy(prepared / (root + '.lean'), 'circuits/ShielddSecurity/' + root + '.lean')
        copy(prepared / 'manifest.json', label + '/inputs/manifest.json')
        for recipe in [local / ('prepare-' + stem + '.py'), local / ('run-safe-' + stem + '.ps1'),
            diag / ('root-' + stem + '.ps1'), diag / ('audit-' + stem + '.py')]:
            copy(recipe, label + '/recipes/' + recipe.name)
    for recipe in [Path(__file__), local / 'make-connected-semantic-preparer-20261009-01.py',
        local / 'check-subgroup-template-layout-20261009-01.py', local / 'check-subgroup-template-layout-20261009-02.py',
        local / 'subgroup-template-layout-check-20261009-02.json']:
        copy(recipe, 'recipes/' + recipe.name)
    resolution = {}
    for label, (stem, boundary, root) in checks.items():
        manifest = load(diag / (stem + '-source/manifest.json'))
        closure = dict(manifest['sources'])
        for item in manifest['reused']:
            closure[item['name']] = {'path': item['original_source'], 'sha256': item['original_source_sha256']}
        resolution[label] = {}
        for name, identity in closure.items():
            candidates = [dest / 'circuits/ShielddSecurity' / (name + '.lean'),
                base / 'sources/mac/mac-connected-subgroup01/final01/project/ShielddSecurity' / (name + '.lean'),
                repo / 'circuits/ShielddSecurity' / (name + '.lean'),
                base / 'sources/windows/maintained-review-20261009-01/formal/circuits/ShielddSecurity' / (name + '.lean'),
                base / 'sources/windows/subgroup-arithmetic-20261009-01/circuits/ShielddSecurity' / (name + '.lean'),
                base / 'sources/windows/foundation-20261009-01/circuits/ShielddSecurity' / (name + '.lean')]
            matches = [p for p in candidates if p.exists() and sha(p) == identity['sha256']]
            assert matches, (label, name, 'exact published dependency required')
            resolution[label][name] = {'path': str(matches[0].relative_to(repo)).replace('\\', '/'), 'sha256': identity['sha256']}
    write(dest / 'dependency-resolution.json', resolution)
    files['dependency-resolution.json'] = {'sha256': sha(dest / 'dependency-resolution.json'), 'bytes': (dest / 'dependency-resolution.json').stat().st_size}
    roster = {'unique_new_template_theorems': 22, 'unique_new_concrete_theorems': 10,
        'template': load(diag / (checks['template'][0] + '-source/manifest.json'))['expected_theorems_by_module'][checks['template'][2]],
        'concrete': load(diag / (checks['concrete'][0] + '-source/manifest.json'))['expected_theorems_by_module'][checks['concrete'][2]],
        'soundness': 'All71 selected original rows under arbitrary rho with rho0=1 imply preimage OnCurve and nativeEight(preimage)=claimed point. Exact graph syntax and all six assertion pairs are closed, with source witness IDs11 through17.',
        'completeness': 'Independent admitted subgroup point constructs native preimage and three shared-product inverse hints, proves all six assertions, and constructs total rho satisfying all71 selected original rows, preserving all22735 source inputs and setting fixed/copy columns to1.',
        'identity_permitted': True, 'two_four_nonzero_derived_from_characteristic': True,
        'residual_premises': ['StandardCurveModel and NoUnitSquare for the fixed source d',
            'Named canonical field decoder and BE writer contracts', 'Imaginary square=-1 and independent subgroup admission',
            'Concrete deployed curve/codec/Crypto and native runtime correspondence',
            'Remaining full Transfer source graph, full-row coverage/LocalRowSoundness and durable state refinement'],
        'failed_template_checks': {'01': 'syntax/tactic imports and elaboration', '02': 'elaboration and proof goals',
            '03': 'finite400000 heartbeat timeout plus elaboration', '04': 'two unresolved zeroth-node equations'},
        'failed_attempt_proof_control_credit': 0, 'full_transfer': 'OPEN', 'native_successors': 'UNRUN'}
    write(dest / 'review-roster.json', roster)
    files['review-roster.json'] = {'sha256': sha(dest / 'review-roster.json'), 'bytes': (dest / 'review-roster.json').stat().st_size}
    write(dest / 'manifest.json', {'files': files, 'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
        'shared_mac_packet_commit': 'efe6a0d050138f7e72d1061a7fe1d39b4aa35cce',
        'scope': 'Handwritten semantic source and exact recipes only. Shared generated data/row proofs are resolved to their already-published exact sources. Actual audit receipts are separate; no logs, objects, caches or certification promotion.', 'full_transfer': 'OPEN'})
    print(json.dumps({'files': len(files), 'manifest_sha256': sha(dest / 'manifest.json')}))
elif phase == 'verify-index':
    for rel, identity in load(dest / 'manifest.json')['files'].items():
        path = str((dest / rel).relative_to(repo)).replace('\\', '/')
        content = subprocess.check_output(['git', '-C', str(repo), 'show', ':' + path])
        assert hashlib.sha256(content).hexdigest() == identity['sha256'], path
    print('Exact source Git index bytes PASS')
elif phase == 'receipts':
    commit = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    refs = {}
    for label, (stem, boundary, root) in checks.items():
        kernel = diag / (stem + '-kernel'); manifest = load(kernel / 'manifest.json')
        modules = {}
        for name in manifest['order']:
            leaf = kernel / name; audit = load(leaf / 'audit.json')
            assert (leaf / 'exit.txt').read_text().strip() == '0' and (leaf / 'end.txt').exists()
            assert not (leaf / 'stop.txt').exists()
            assert sha(kernel / 'project/ShielddSecurity' / (name + '.lean')) == audit['candidate_sha256'] == manifest['audited_candidates'][name]
            assert audit['full_types_checked']
            for used in audit['axioms'].values(): assert set(used) <= {'propext', 'Classical.choice', 'Quot.sound'}
            modules[name] = {'audit': audit, 'actual_exit': 0,
                'stdout_sha256': sha(leaf / 'stdout.txt'), 'stderr_sha256': sha(leaf / 'stderr.txt')}
        root_audits = len(manifest['expected_theorems_by_module'][root])
        total = sum(m['audit']['audits'] for m in modules.values())
        receipt = {'runtime_sha': manifest['runtime_sha'], 'source_commit': commit,
            'source_packet_manifest_sha256': sha(dest / 'manifest.json'), 'source_index_exact_bytes_verified': True,
            'source_diff_check': 'FAILED_EXACT_PRODUCER_RECIPE_CRLF_OR_TERMINAL_BLANK_LINES; checked bytes retained',
            'preparation_manifest_sha256': sha(kernel / 'manifest.json'), 'recipe': load(kernel / 'recipe.json'),
            'fresh_modules': len(modules), 'unique_new_root_theorems': root_audits, 'fresh_dependency_replay_audits': total - root_audits,
            'qualified_reused_modules': len(manifest['reused']), 'total_audits': total,
            'actual_exit': 0, 'root_resume_status': 0, 'modules': modules,
            'external_cache_before_sha256': sha(kernel / 'external-before.json'), 'external_cache_identity_rechecked': True,
            'start': (kernel / 'start.txt').read_text().strip(), 'end': (kernel / 'end.txt').read_text().strip(),
            'scope': manifest['scope'], 'full_transfer': 'OPEN', 'native_successors': 'UNRUN'}
        path = base / f'receipts/windows/connected-subgroup-{label}-20261009-01.json'
        assert not path.exists(); write(path, receipt)
        refs[label] = {'path': str(path.relative_to(base)).replace('\\', '/'), 'sha256': sha(path)}
    status_path = base / 'status/windows.json'; status = load(status_path)
    journal = load(diag / 'root-dh-primary-joint-after-initialization-2516-successor-3130/journal.json')
    status['snapshot_utc'] = datetime.now(timezone.utc).isoformat()
    status['synchronized_origin_sha'] = 'efe6a0d050138f7e72d1061a7fe1d39b4aa35cce'
    status['active_controller'].update({'settled_dh_phases': len(journal), 'settled_dh_modules': sum(x.get('modules', 0) for x in journal),
        'settled_dh_audits': sum(x.get('exports', 0) for x in journal),
        'whole_root_complete': (diag / 'root-field-native-epk-cast-repair-3130/complete.txt').exists()})
    status['checked_connected_subgroup_semantics_20261009_01'] = {'source_commit': commit, 'receipts': refs,
        'unique_new_theorems': 32, 'selected_original_rows': 71, 'preserved_source_inputs': 22735,
        'independent_six_assertions': True, 'identity_permitted': True, 'full_transfer': 'OPEN'}
    write(status_path, status)
    print(json.dumps({'source_commit': commit, 'receipts': refs, 'settled_dh_phases': len(journal)}))
else: raise ValueError(phase)
