from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, statistics

root = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
out = Path('C:/src/shieldd-transfer-handoffs/windows-native-backlog-20261009-01.json')
assert not out.exists()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
dt = lambda s: datetime.fromisoformat(s.strip().replace('Z', '+00:00'))
journal = load(root / 'root-dh-primary-joint-after-initialization-2516-successor-3130/journal.json')
plan = load(root / 'field-native-epk-serial-recipes-3130/plan.json')
pauses = []
for p in root.glob('safe-*-20261009*'):
    if all((p/n).exists() for n in ['suspended-at-safe-boundary.txt', 'resume-status.txt', 'end.txt']):
        assert (p/'resume-status.txt').read_text().strip() == '0'
        pauses.append((dt((p/'suspended-at-safe-boundary.txt').read_text()), dt((p/'end.txt').read_text())))
recent = []
for item in journal[-6:]:
    batch = Path(item['batch'])
    starts = list(batch.glob('*/start.txt'))
    ends = list(batch.glob('*/end.txt'))
    start, end = min(dt(p.read_text()) for p in starts), max(dt(p.read_text()) for p in ends)
    paused = sum(max(0, (min(end, b)-max(start, a)).total_seconds()) for a,b in pauses)
    recent.append({'role': item['role'], 'phase': item['phase'],
        'kernel_span_seconds': (end-start).total_seconds(), 'recorded_owned_pause_seconds': paused,
        'span_excluding_recorded_pauses_seconds': (end-start).total_seconds()-paused,
        'timed_leaf_build_seconds': sum((dt((p.parent/'end.txt').read_text())-dt(p.read_text())).total_seconds() for p in starts)})
native = [
    ('root-full-transfer-native-suite-3057.ps1', 'run-full-transfer-native-suite-2981.py', 'full-transfer-native-suite-2981',
     ['whole3130 actual terminal exit0 including separately retained anticipated preflight failures', 'raw-statement-current-project-kernel-3117 actual success', 'registry-user-current-project-kernel-3046 actual success', 'exact clean844 source tar and six formal-owned tests'],
     'Six genuine Transfer proof/admission/effects/cache tests; complete matching seven-family development keys.'),
    ('root-transfer-native-recovery-3058.ps1', 'run-transfer-native-recovery-2983.py', 'transfer-native-recovery-2983',
     ['full-transfer-native-suite-2981 actual complete exit0', 'same exact source and development key inventories'],
     'Eleven permanent-nullifier/NOMT recovery tests and eight SCT persistence tests. Crash worker excluded from standalone enumeration; intended crash statuses are checked by the parent test.'),
    ('root-transfer-cross-key-native-3059.ps1', 'run-transfer-cross-key-native-2988.py', 'transfer-cross-key-native-2988',
     ['transfer-native-recovery-2983 actual complete exit0', 'independent second development registry with identical relation labels and a distinct Transfer verifying-key digest'],
     'One actual same-family/same-relation/different-verifying-key admission control.'),
    ('root-transfer-sct-root-native-3060.ps1', 'run-transfer-sct-root-native-2993.py', 'transfer-sct-root-native-2993',
     ['actual full native suite results/keys', 'initial-witness-current-project-kernel-3040 actual success and original2990 receipt required by driver', 'fresh snapshot source/stage/target identities'],
     'Six existing genuine Transfer tests repeated against the source-bound SCT-root snapshot; not six additional independent controls.')]
native_records = []
for controller, driver, namespace, dependencies, scope in native:
    assert not (root/namespace).exists()
    native_records.append({'controller': controller, 'controller_sha256': sha(root/controller),
        'driver': driver, 'driver_sha256': sha(root/driver), 'output_namespace': namespace,
        'actual_run': False, 'dependencies': dependencies, 'scope': scope})
statement = root/'raw-statement-current-project-kernel-3117'
assert all((statement/n).exists() for n in ['end.txt', 'complete.txt', 'exit.txt'])
assert (statement/'exit.txt').read_text().strip() == '0' and not (statement/'stop.txt').exists()
result = {'snapshot_utc': datetime.now(timezone.utc).isoformat(),
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'whole_3130_complete': (root/'root-field-native-epk-cast-repair-3130/complete.txt').exists(),
    'settled_dh_loop_phases': sum(x['kind']=='loop' for x in journal),
    'settled_dh_modules': sum(x['modules'] for x in journal), 'settled_dh_audits': sum(x['exports'] for x in journal),
    'remaining_dh_loop_phases': 75-sum(x['kind']=='loop' for x in journal),
    'remaining_scalar_join_phases': 5-sum(x['kind']=='scalar' for x in journal),
    'recent_measured_kernel_spans': recent,
    'median_recent_span_excluding_recorded_pauses_seconds': statistics.median(x['span_excluding_recorded_pauses_seconds'] for x in recent),
    'timing_scope': 'Timed Lean kernel span only; metadata preparation, subsequent24 controllers, safe-boundary waits and native jobs are excluded. Not a full-chain ETA.',
    'after_current_dh': [{'controller': n+'.ps1', 'sha256': plan['files'][n+'.ps1']} for n in plan['order'][3:]],
    'statement3117': {'actual_complete_exit': 0, 'scope': (statement/'complete.txt').read_text().strip()},
    'native': native_records,
    'fresh_coordinator_requirement': 'Prepared controllers retain older local predecessor guards. Create a new immutable coordinator only after actual whole3130 and3117 success; retain original drivers/source bytes. Do not launch stale3124/3118/3114/3089 coordinators.',
    'state_backlog': {'formal_modules': ['TransferFullCarrierAcceptance', 'TransferTransaction', 'TransferExecution', 'TransferIndexing'],
        'model_runtime_command': 'python security.py state', 'model_only_command': 'python security.py state --model-only',
        'checker': 'state/check.py', 'runtime_control_manifest': 'state/transfer_effect_controls.json',
        'remaining': ['Bind actual prepared carrier, verified capabilities, full compiler relation and all spend/effect slots to formal model',
            'Execute native admission/effects/cache tests and crash/WAL/application-commit recovery tests at exact844',
            'Check staged routing/index rollback and both index modes against durable snapshots',
            'Keep bounded model-checking and runtime replay evidence separate; no abstract indexing theorem is a durable native refinement',
            'Atomic evidence refresh only when relevant formal/native/model gates actually pass']},
    'symbolic_optimization': {'existing_candidates': ['GroupCircuitProgramTrace.run_append', 'GroupCircuitProgramTrace.aligned_append', 'GroupCircuitFrameTrace.certified_append', 'ScalarRows.checked_chain_sound', 'GroupVariableCircuitSoundness.checked_native', 'GroupVariableCircuitCompletion.constructs'],
        'assessment': 'These symbolic recurrences can compose generic steps and support/write frames. They do not discharge unchanged exact concrete DH row/source certificates by themselves. Replacing720 concrete leaf checks requires an independently checked shared template/renaming/row matcher and coherent dependency proof. No safe drop-in change to the frozen active recipe is established.',
        'active_jobs_interrupted_to_optimize': False}, 'full_transfer': 'OPEN'}
out.write_bytes((json.dumps(result,indent=2)+'\n').encode())
print(json.dumps({'backlog':str(out), 'sha256':sha(out), 'settled_dh_phases':result['settled_dh_loop_phases'],
    'remaining_loop_phases':result['remaining_dh_loop_phases'], 'median_recent_kernel_span_seconds':result['median_recent_span_excluding_recorded_pauses_seconds']}))
