from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys

repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
base = repo / 'handoffs/transfer-20261009'
dest = base / 'sources/windows/subgroup-arithmetic-20261009-01'
stem = 'windows-subgroup-arithmetic-20261009-03'
kernel = diag / (stem + '-kernel')
prepared = diag / (stem + '-source')
boundary = diag / 'safe-subgroup-arithmetic-boundary-2026100903'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
write = lambda p, value: p.write_bytes((json.dumps(value, indent=2) + '\n').encode())
manifest = load(prepared / 'manifest.json')
assert (kernel / 'complete.txt').exists() and (kernel / 'end.txt').exists()
assert (kernel / 'exit.txt').read_text().strip() == '0'
assert (boundary / 'resume-status.txt').read_text().strip() == '0'
assert (boundary / 'exit.txt').read_text().strip() == '0'
phase = sys.argv[1]
if phase == 'sources':
    assert not dest.exists()
    dest.mkdir(parents=True)
    files = {}
    def copy(source, relative):
        target = dest / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(source.read_bytes())
        assert sha(source) == sha(target)
        files[relative] = {'sha256': sha(target), 'bytes': target.stat().st_size}
    root = 'GroupSubgroupGraphArithmetic'
    copy(prepared / (root + '.lean'), 'circuits/ShielddSecurity/' + root + '.lean')
    resolution = {}
    for name, identity in manifest['sources'].items():
        candidates = [dest / 'circuits/ShielddSecurity' / (name + '.lean'),
            repo / 'circuits/ShielddSecurity' / (name + '.lean'),
            base / 'sources/windows/maintained-review-20261009-01/formal/circuits/ShielddSecurity' / (name + '.lean')]
        exact = [p for p in candidates if p.exists() and sha(p) == identity['sha256']]
        assert exact, ('exact published dependency required', name)
        resolution[name] = {'path': str(exact[0].relative_to(repo)).replace('\\', '/'), 'sha256': identity['sha256']}
    write(dest / 'dependency-resolution.json', resolution)
    files['dependency-resolution.json'] = {'sha256': sha(dest / 'dependency-resolution.json'), 'bytes': (dest / 'dependency-resolution.json').stat().st_size}
    copy(prepared / 'manifest.json', 'inputs/manifest.json')
    cache = load(kernel / 'cache-inputs.json')
    cache_identity = {'original_manifest_sha256': sha(kernel / 'cache-inputs.json'),
        **{key: cache[key] for key in ['scope', 'packages', 'external_modules', 'bytes']}}
    write(dest / 'inputs/cache-identity.json', cache_identity)
    files['inputs/cache-identity.json'] = {'sha256': sha(dest / 'inputs/cache-identity.json'), 'bytes': (dest / 'inputs/cache-identity.json').stat().st_size}
    for recipe in [local / 'prepare-windows-subgroup-arithmetic-20261009-01.py',
        local / 'prepare-windows-subgroup-arithmetic-20261009-02.py',
        local / 'fix-subgroup-preparation-20261009-03.py',
        local / ('prepare-' + stem + '.py'), local / ('run-safe-' + stem + '.ps1'),
        diag / ('root-' + stem + '.ps1'), diag / ('audit-' + stem + '.py'), Path(__file__)]:
        copy(recipe, 'recipes/' + recipe.name)
    for name in ['windows-native-backlog-20261009-01.json', 'windows-native-state-boundary-alignment-20261009-01.json',
        'snapshot-windows-native-backlog-20261009-01.py', 'snapshot-state-boundary-alignment-20261009-01.py']:
        copy(local / name, 'native/' + name)
    roster = {'new_theorems': manifest['expected_theorems_by_module'][root],
        'conclusions': 'Exact7-node curve and17-node shared-product inverse doubling arithmetic. Symbolic recurrence composes three doublings. Six source assertion equations derive OnCurve preimage and nativeEight=point; completion constructs shared inverse hints from independent OnCurve and nonzero-denominator conditions.',
        'residual_obligations': ['Typed graph-syntax matcher and concrete extracted80-node instance',
            'All71 original indexed row bodies and forward/reverse coverage',
            'Named curve/codec/native SDK interpretation and concrete deployed Crypto instance',
            'Full graph partition, LocalRowSoundness and complete Transfer carrier/runtime/state refinement'],
        'dependency_replays': 193, 'unique_new_theorems': 13,
        'preflight_failures': {'01': 'word axiom in dependency documentation; Lean not started',
            '02': 'comment-stripped offsets accidentally used for audit insertion; proof-byte invariant failed, Lean not started'},
        'failed_attempt_credit': 0, 'native_successors': 'UNRUN', 'full_transfer': 'OPEN'}
    write(dest / 'review-roster.json', roster)
    files['review-roster.json'] = {'sha256': sha(dest / 'review-roster.json'), 'bytes': (dest / 'review-roster.json').stat().st_size}
    write(dest / 'manifest.json', {'files': files, 'runtime_sha': manifest['runtime_sha'],
        'scope': 'Exact handwritten arithmetic source, check recipes and native/state backlog. Actual kernel receipts are published separately; no logs, objects, prover cache or certification promotion.', 'full_transfer': 'OPEN'})
    print(json.dumps({'files': len(files), 'manifest_sha256': sha(dest / 'manifest.json')}))
elif phase == 'compact-input':
    packet = load(dest / 'manifest.json')
    old = dest / 'inputs/cache-inputs.json'
    assert sha(old) == sha(kernel / 'cache-inputs.json')
    cache = load(old)
    write(dest / 'inputs/cache-identity.json', {'original_manifest_sha256': sha(old),
        **{key: cache[key] for key in ['scope', 'packages', 'external_modules', 'bytes']}})
    old.unlink()
    del packet['files']['inputs/cache-inputs.json']
    for relative, source in [('inputs/cache-identity.json', dest / 'inputs/cache-identity.json'),
        ('recipes/' + Path(__file__).name, Path(__file__))]:
        target = dest / relative
        if target != source: target.write_bytes(source.read_bytes())
        packet['files'][relative] = {'sha256': sha(target), 'bytes': target.stat().st_size}
    write(dest / 'manifest.json', packet)
    print(json.dumps({'manifest_sha256': sha(dest / 'manifest.json')}))
elif phase == 'verify-index':
    for relative, identity in load(dest / 'manifest.json')['files'].items():
        path = str((dest / relative).relative_to(repo)).replace('\\', '/')
        raw = subprocess.check_output(['git', '-C', str(repo), 'show', ':' + path])
        assert hashlib.sha256(raw).hexdigest() == identity['sha256'], path
    print('Exact Git source index bytes PASS')
elif phase == 'receipts':
    commit = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    modules = {}
    for name in manifest['order']:
        leaf = kernel / name
        audit = load(leaf / 'audit.json')
        assert (leaf / 'end.txt').exists() and (leaf / 'exit.txt').read_text().strip() == '0'
        assert not (leaf / 'stop.txt').exists()
        source = kernel / 'project/ShielddSecurity' / (name + '.lean')
        assert sha(source) == audit['candidate_sha256'] == manifest['audited_candidates'][name]
        assert audit['full_types_checked']
        for used in audit['axioms'].values():
            assert set(used) <= {'propext', 'Classical.choice', 'Quot.sound'}
        modules[name] = {'audit': audit, 'exit': 0, 'stdout_sha256': sha(leaf / 'stdout.txt'),
            'stderr_sha256': sha(leaf / 'stderr.txt'), 'start': (leaf / 'start.txt').read_text().strip(),
            'end': (leaf / 'end.txt').read_text().strip()}
    path = base / 'receipts/windows/subgroup-arithmetic-20261009-01.json'
    assert not path.exists()
    receipt = {'runtime_sha': manifest['runtime_sha'], 'source_commit': commit,
        'source_packet': str(dest.relative_to(base)).replace('\\', '/'), 'source_packet_manifest_sha256': sha(dest / 'manifest.json'),
        'preparation_manifest_sha256': sha(prepared / 'manifest.json'), 'source_index_exact_bytes_verified': True,
        'source_diff_check': 'FAILED_FROZEN_PRODUCER_CRLF_TERMINAL_BLANK_LINES; exact checked bytes retained',
        'actual_exit': 0, 'fresh_modules': len(modules), 'root_new_theorems': 13,
        'dependency_replay_audits': 193, 'total_audits': 206, 'root_resume_status': 0,
        'recipe': load(kernel / 'recipe.json'), 'scope': manifest['scope'], 'modules': modules,
        'external_cache_before_sha256': sha(kernel / 'external-before.json'),
        'external_cache_identity_rechecked': True,
        'start': (kernel / 'start.txt').read_text().strip(), 'end': (kernel / 'end.txt').read_text().strip(),
        'native_successors': 'UNRUN', 'full_transfer': 'OPEN'}
    write(path, receipt)
    status_path = base / 'status/windows.json'
    status = load(status_path)
    journal = load(diag / 'root-dh-primary-joint-after-initialization-2516-successor-3130/journal.json')
    status['snapshot_utc'] = datetime.now(timezone.utc).isoformat()
    status['synchronized_origin_sha'] = '2c1539d02fe62041aaf451598ccb348973c38366'
    status['active_controller'].update({'settled_dh_phases': len(journal),
        'settled_dh_modules': sum(x.get('modules', 0) for x in journal),
        'settled_dh_audits': sum(x.get('exports', 0) for x in journal),
        'whole_root_complete': (diag / 'root-field-native-epk-cast-repair-3130/complete.txt').exists()})
    status['checked_subgroup_arithmetic_20261009_01'] = {'source_commit': commit,
        'receipt': str(path.relative_to(base)).replace('\\', '/'), 'receipt_sha256': sha(path),
        'new_theorems': 13, 'dependency_replays': 193, 'root_resume_status': 0,
        'typed_graph_bridge': 'SOURCE_DRAFT; first failed check earns zero proof credit', 'full_transfer': 'OPEN'}
    status['native_backlog_20261009_01'] = {'path': str((dest / 'native/windows-native-backlog-20261009-01.json').relative_to(base)).replace('\\', '/'),
        'sha256': sha(dest / 'native/windows-native-backlog-20261009-01.json'),
        'state_boundary_alignment_path': str((dest / 'native/windows-native-state-boundary-alignment-20261009-01.json').relative_to(base)).replace('\\', '/'),
        'state_boundary_alignment_sha256': sha(dest / 'native/windows-native-state-boundary-alignment-20261009-01.json')}
    write(status_path, status)
    print(json.dumps({'source_commit': commit, 'receipt_sha256': sha(path), 'settled_dh_phases': len(journal)}))
else:
    raise ValueError(phase)
