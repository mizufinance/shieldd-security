from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys

repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
local = Path('C:/src/shieldd-transfer-handoffs')
packet = local / 'windows-foundation-20261009-01'
dest = repo / 'handoffs/transfer-20261009/sources/windows/foundation-20261009-01'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
write = lambda p, value: p.write_bytes((json.dumps(value, indent=2) + '\n').encode())
phase = sys.argv[1]
if phase == 'sources':
    assert not dest.exists(), 'fresh frozen source destination required'
    dest.mkdir(parents=True)
    files = {}
    def copy(source, relative):
        target = dest / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(source.read_bytes())
        assert sha(source) == sha(target)
        files[relative] = {'source_sha256': sha(source), 'bytes': source.stat().st_size}
    for rel, identity in load(packet / 'manifest.json')['files'].items():
        if rel.startswith('circuits/'):
            assert sha(packet / rel) == identity['sha256']
            copy(packet / rel, rel)
    for suffix in ['05', '06']:
        stem = f'windows-graph-input-bridge-20261009-{suffix}'
        copy(local / f'prepare-{stem}.py', f'recipes/prepare-{stem}.py')
        copy(local / f'run-safe-{stem}.ps1', f'recipes/run-safe-{stem}.ps1')
        copy(diag / f'root-{stem}.ps1', f'recipes/root-{stem}.ps1')
        copy(diag / f'audit-{stem}.py', f'recipes/audit-{stem}.py')
        copy(diag / (stem + '-source') / 'manifest.json', f'inputs/{stem}-manifest.json')
    copy(diag / 'native-host-memory-api-01.ps1', 'recipes/native-host-memory-api-01.ps1')
    copy(local / 'prepare-windows-foundation-packet-20261009-01.py', 'recipes/prepare-windows-foundation-packet-20261009-01.py')
    copy(Path(__file__), 'recipes/publish-windows-foundation-20261009-01.py')
    write(dest / 'manifest.json', {'files': files, 'runtime_sha': load(packet / 'receipt.json')['runtime_sha'],
        'scope': 'Three handwritten symbolic bridge modules and exact local source/check recipes; no objects, raw logs, caches or release evidence.',
        'dependencies': 'Existing maintained-review-20261009-01 and kernel-pilot-20261009-01 source transports; actual imported source/object hashes retained in inputs for identity only.',
        'reproduction': 'Recipes retain original Windows diagnostic paths. Independent replay requires rebuilding the recorded source closure with the exact Lean/Mathlib pins; these paths do not make this transport a portable proof cache.',
        'full_transfer': 'OPEN'})
    print(json.dumps({'source_manifest_sha256': sha(dest / 'manifest.json'), 'source_files': len(files)}))
elif phase == 'verify-index':
    manifest = load(dest / 'manifest.json')
    for rel, identity in manifest['files'].items():
        path = str((dest / rel).relative_to(repo)).replace('\\', '/')
        indexed = subprocess.check_output(['git', '-C', str(repo), 'show', ':' + path])
        assert hashlib.sha256(indexed).hexdigest() == identity['source_sha256'], path
    print(json.dumps({'exact_git_index_source_files': len(manifest['files'])}))
elif phase == 'receipts':
    source_commit = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    receipt = load(packet / 'receipt.json')
    receipt['publication_status'] = 'SOURCE_COMMIT_AND_ACTUAL_LOCAL_KERNEL_RECEIPTS'
    receipt['source_commit'] = source_commit
    receipt['source_packet'] = str(dest.relative_to(repo / 'handoffs/transfer-20261009')).replace('\\', '/')
    receipt['source_manifest_sha256'] = sha(dest / 'manifest.json')
    receipt['local_review_manifest_sha256'] = sha(packet / 'manifest.json')
    receipt['local_review_receipt_sha256'] = sha(packet / 'receipt.json')
    receipt['source_index_verification'] = {'files': len(load(dest / 'manifest.json')['files']), 'exact_bytes': True}
    receipt['source_diff_check'] = {'result': 'FAILED_EXISTING_FROZEN_RECIPE_WHITESPACE',
        'scope': 'Four exact producer preparation/boundary scripts retain terminal CRLF blank lines. Producer bytes preserved; this is not a kernel or semantic-control result.'}
    for failure in receipt['preserved_failures']:
        suffix = failure['suffix']
        batch = diag / f'windows-graph-input-bridge-20261009-{suffix}-kernel'
        assert (batch / 'exit.txt').read_text().strip() == '1' and (batch / 'end.txt').exists()
        assert not (batch / 'complete.txt').exists()
        failure.update({'actual_exit': 1, 'manifest_sha256': sha(batch / 'manifest.json'),
            'failure_sha256': sha(batch / 'failure.txt'),
            'failing_seed_stdout_sha256': sha(batch / 'TransferCircuitInputSeed/stdout.txt'),
            'root_resume_status': int((diag / f'safe-inverse-boundary-20261009{suffix}/resume-status.txt').read_text().strip())})
    receipt['native_successors'] = []
    for controller, namespace in [('3057', 'full-transfer-native-suite-2981'),
        ('3058', 'transfer-native-recovery-2983'), ('3059', 'transfer-cross-key-native-2988'),
        ('3060', 'transfer-sct-root-native-2993')]:
        assert not (diag / namespace).exists(), 'native namespace changed; inspect actual results'
        receipt['native_successors'].append({'controller_id': controller, 'output_namespace': namespace, 'actual_run': False})
    journal = load(diag / 'root-dh-primary-joint-after-initialization-2516-successor-3130/journal.json')
    settled = {'phases': len(journal), 'modules': sum(x.get('modules', 0) for x in journal),
               'audits': sum(x.get('exports', 0) for x in journal)}
    receipt['observed_utc'] = datetime.now(timezone.utc).isoformat()
    receipt['serial_3130'] = {'settled_dh': settled,
        'whole_root_complete': (diag / 'root-field-native-epk-cast-repair-3130/complete.txt').exists(),
        'plan_sha256': sha(diag / 'field-native-epk-serial-recipes-3130/plan.json'),
        'guard_sha256': sha(diag / 'root-field-native-epk-cast-repair-3130.ps1')}
    target = repo / 'handoffs/transfer-20261009/receipts/windows/foundation-20261009-01.json'
    assert not target.exists()
    write(target, receipt)
    status_path = repo / 'handoffs/transfer-20261009/status/windows.json'
    status = load(status_path)
    status['snapshot_utc'] = receipt['observed_utc']
    status['synchronized_origin_sha'] = receipt['publication_base_observed']
    status['active_controller'].update({'settled_dh_phases': settled['phases'],
        'settled_dh_modules': settled['modules'], 'settled_dh_audits': settled['audits'],
        'whole_root_complete': receipt['serial_3130']['whole_root_complete']})
    status['checked_foundation_20261009_01'] = {'source_commit': source_commit,
        'source_packet': receipt['source_packet'], 'source_manifest_sha256': receipt['source_manifest_sha256'],
        'receipt': 'receipts/windows/foundation-20261009-01.json', 'receipt_sha256': sha(target),
        'unique_new_audits': 13, 'checks_total_including_replays': [21, 23],
        'safe_root_resumes': [0, 0], 'full_transfer': 'OPEN', 'native_successors_run': False}
    status['current_publication_lock'] = {'runtime_sha': load(repo / 'shieldd.lock')['sha'],
        'reconciled_by_parent': True, 'historical_source_only_lock_mismatch_receipts_retained': True}
    status['implementation_assignment'] = 'Windows proof/native lane; sole existing3130 verifier active. Parent owns maintained integration; Mac owns full compiler pilot. Foundation checks complete, full semantic/row/native closure OPEN.'
    write(status_path, status)
    print(json.dumps({'receipt_sha256': sha(target), 'source_commit': source_commit, 'settled_dh': settled}))
else:
    raise ValueError(phase)
