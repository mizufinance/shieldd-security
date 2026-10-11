"""Read-only milestone status; retained producer reports confer no new credit."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
D=DIAG/'transfer-implementation-20261002'
def pin(path):
    path=Path(path)
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
def optional(path):
    return pin(path) if path.is_file() else None
plan_path=D/'field-native-epk-serial-recipes-3130/plan.json'
plan=json.loads(plan_path.read_text())
controllers=[]
for name in plan['order']:
    task=D/name
    journal_path=task/'journal.json'
    journal=json.loads(journal_path.read_text()) if journal_path.is_file() else []
    entries=journal if isinstance(journal,list) else [journal]
    controllers.append({'task':name,'journal':optional(journal_path),'records':len(entries),
        'reported_modules':sum(e.get('modules',0) for e in entries),
        'reported_exports':sum(e.get('exports',0) for e in entries),
        'last_report':entries[-1] if entries else None,
        'complete':optional(task/'complete.txt'),'exit':optional(task/'exit.txt'),
        'exit_text':(task/'exit.txt').read_text().strip() if (task/'exit.txt').is_file() else None})
dh=next(c for c in controllers if c['task']=='root-dh-primary-joint-after-initialization-2516-successor-3130')
assert dh['records']==69 and dh['last_report']['role']==4 and dh['last_report']['phase']==8
native_plan_path=D/'full-transfer-native-plan-2999-dh-recovery-3017-semantic-3057.json'
native_plan=json.loads(native_plan_path.read_text())
assert native_plan['status']=='SOURCE_ONLY_UNLAUNCHED'
execution_manifest_path=D/'transfer-v2-five-controls-execution-04/manifest.json'
execution_manifest=json.loads(execution_manifest_path.read_text())
jobs=[]
for job in execution_manifest['jobs']:
    output=D/job['output']
    jobs.append({'test':job['name'],'output':str(output),'directory_exists':output.exists(),
        'exit_text':(output/'exit.txt').read_text().strip() if (output/'exit.txt').is_file() else None,
        'stdout':optional(output/'stdout.txt'),'stderr':optional(output/'stderr.txt')})
direct=[]
for task_name in ['runtime-transfer-direct-01','runtime-transfer-expanded-direct-02']:
    task=D/task_name
    stdout=(task/'stdout.txt').read_text()
    direct.append({'task':task_name,'recorded_test_result':stdout.strip(),
        'records':[pin(task/name) for name in ['stdout.txt','stderr.txt','exit.txt','source-inputs.txt','source-inputs-after.txt','executed-inputs.txt','executed-inputs-after.txt']],
        'qualification':'Retained positive branch circuit tests; source/binary/dependency identities need current validation before reuse, and these are not genuine app/state/durability coverage.'})
own=[]
for task_name in ['transfer-proof-admission-20261010-02','transfer-envelope-source-bridge-20261010-01','transfer-capability-envelope-join-20261010-01']:
    task=DIAG/task_name
    events=[json.loads(line) for line in (task/'events.jsonl').read_text().splitlines()]
    passed=[e for e in events if e['event']=='attempt_finished' and e['result']['status']=='passed']
    assert len(passed)==1
    own.append({'task':task_name,'plan':pin(task/'plan.json'),'events':pin(task/'events.jsonl'),
                'module':passed[0]['module'],'audit_pairs':len(passed[0]['result']['audits']),
                'receipt':passed[0]['result']})
status={'kind':'READ_ONLY_TRANSFER_COMPLETION_MILESTONE','runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
        'latest_parent_canonical_sha':'67aa4dc327946667d0a542851470dd2e0d33cd2b',
        'own_envelope_join':{'status':'KERNEL_PASSED_SCOPED_ASSOCIATION','sources':3,'audit_pairs':35,'phases':own,
            'scope':'Exact retained-envelope/local-relation/location-family/claim framing at every constructor-checked slot. Native extraction/container/codec/key/crypto semantics remain open; no per-entry batch knowledge consequence.'},
        'retained3130':{'plan':pin(plan_path),'status':'PARTIAL_RETAINED_PRODUCER_JOURNALS','controllers':controllers,
            'remaining':['DH primary role4 loop phases09..14 remain uncompleted after69 reports/666 modules/1367 exports; the controller has no completion or exit receipt.',
                'All subsequent24 controller stages remain separate prerequisites; inspect their own receipts and frozen source/import plans before any fresh continuation.',
                'Source/primitive/circuit-cache/caller correspondence is distinct from the retained model reports. Source/hash checks alone do not establish it.'],
            'new_proof_credit':0},
        'native_suite':{'plan':pin(native_plan_path),'status':native_plan['status'],'output_directory_exists':(D/'full-transfer-native-suite-2981').exists(),
            'declared_parent':native_plan['parent'],'frozen_dependencies':native_plan['frozen'],'phases':native_plan['phases'],
            'remaining':['Validate exact frozen source and test-only overlay against the clean full runtime SHA, plus actual current prerequisite receipts; retire passive wait dependencies in a fresh reviewed plan.',
                'Schedule a fresh isolated guarded source extraction, build, seven-family development setup, app build and exact test inventory; keep one heavy process and physical/commit/disk checks.',
                'Run all separately named genuine proof/admission/state/cache tests; only intended semantic results count, not compiler failures, stops or timeouts.'],
            'new_runtime_credit':0},
        'pinned_runtime_state_tests':{'retained_execution_manifest':pin(execution_manifest_path),'jobs':jobs,'partial_branch_tests':direct,
            'setup_manifest':pin(D/'transfer-v2-five-setup06-successor-02/registry-published.json'),
            'setup_boundary':'Retained setup/publication report explicitly does not establish PK decoding, embedded-VK match or genuine proving; Registry::prove checks these lazily.',
            'remaining':['The first genuine effect test in execution04 exited15 without a completed semantic test result; the remaining13 named outputs in that plan are absent. Neither that stop nor absence is a successful negative control.',
                'Inspect later coherent/delayed-volume/remaining-control successors before declaring final runtime coverage; no new tests were run by this read-only milestone.',
                'Native permanent writer can commit before later fallible completion. Queue draining can precede a fallible store step. Prove and test actual partial-progress/recovery behavior; do not assume all errors restore old state.'],
            'new_runtime_credit':0},
        'g3_g4_dependency':'Exact full-row/copy provider and circuit-to-native semantic composition are Mac-owned pending work; owned implementation and state/durable recovery joins remain required.',
        'runtime_test_credit':0,'semantic_negative_control_credit':0,'native_source_correspondence_credit':0,
        'full_transfer':'OPEN','certification':False,'recipe':pin(Path(__file__))}
target=ROOT/'status.json';assert not target.exists()
target.write_text(json.dumps(status,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':pin(target),'own_envelope_audits':35,'retained3130_records':69,
    'native_suite':'SOURCE_ONLY_UNLAUNCHED','runtime_state_tests':'INCOMPLETE_RETAINED_RECEIPTS','full_transfer':'OPEN','certification':False}))
