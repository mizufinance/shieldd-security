"""Reuse original recovery object/reports once and prepare the writer completion model join."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-authenticated-boundary-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-boundary-reader-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-authenticated-boundary-source-20261011-01'")
replace("POOL = DIAG / 'transfer-authenticated-boundary-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-writer-recovery-join-owned-floor-20261011-01'")
replace("MODULE = 'TransferAuthenticatedBoundarySource01'", "MODULE = 'TransferWriterRecoveryJoin01'")
replace("stdout = UPSTREAM / 'runs/01-TransferBoundaryReaderSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferAuthenticatedBoundarySource01/stdout.txt'")
replace("records.append(('TransferBoundaryReaderSource01'", "records.append(('TransferAuthenticatedBoundarySource01'")
replace("'repair_recipe.py', 'handwritten/TransferBoundaryReaderSource01.lean', 'project/ShielddSecurity/TransferBoundaryReaderSource01.lean'", "'handwritten/TransferAuthenticatedBoundarySource01.lean', 'project/ShielddSecurity/TransferAuthenticatedBoundarySource01.lean'")
replace('assert len(current) == 7','assert len(current) == 9')
replace('assert len(records) == 55 and len(audits) == 551','assert len(records) == 57 and len(audits) == 570')
replace("'objects': 55", "'objects': 57")
s=s.replace('Complete fifty-five-module first owned root; 551 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete fifty-seven-module first owned root; 570 inherited full reports; shared StateDelta/Readback included exactly once. Original BankRecovery10 selected once without replay; WriterPublication not selected.')
replace('assert len(names) == 9','assert len(names) == 6')
replace("'imports': ['ShielddSecurity.TransferBoundaryReaderSource01']", "'imports': ['ShielddSecurity.TransferAuthenticatedBoundarySource01', 'ShielddSecurity.TransferBankRecovery']")
anchor='assert len(records) == 57 and len(audits) == 570'; assert s.count(anchor)==1
extra="""legacy = DIAG / 'transfer-readback-recovery-publication-20261010-02'
legacy_plan = json.loads((legacy / 'plan.json').read_bytes())
legacy_events = [json.loads(row) for row in (legacy / 'events.jsonl').read_text().splitlines()]
legacy_targets = {row['module']: row for row in legacy_plan['targets']}
legacy_results = {row['module']: row['result'] for row in legacy_events if row['event'] == 'attempt_finished'}
assert all(row['status'] == 'passed' for row in legacy_results.values())
shared = next(row for row in records if row[0] == 'TransferReadback')
assert shared[1] == legacy_targets['TransferReadback']['source'] and shared[2] == legacy_results['TransferReadback']['objects'][0]
assert {name: audits[name] for name in legacy_targets['TransferReadback']['audit_names']} == legacy_results['TransferReadback']['audits']
bank = legacy_targets['TransferBankRecovery']; bank_result = legacy_results['TransferBankRecovery']
bank_stdout = legacy / 'runs/02-TransferBankRecovery/stdout.txt'
bank_reports = m.audit(bank_stdout.read_text(), bank['audit_names'])
assert len(bank_reports) == 10 and bank_reports == bank_result['audits']
assert pin(bank_stdout) == bank_result['stdout'] and pin(bank['source']['path']) == bank['source']
assert bank['source']['sha256'] == '446f60161277bab78888eb47dc528a8bc0b9c05283ecf44a59424b0860faa294'
assert pin(bank_result['objects'][0]['path']) == bank_result['objects'][0]
assert bank_result['objects'][0]['sha256'] == '044a20e3830fbe861cfdfa7fd9fbf3df9cd0dc130105999d7f702882a180fd14'
assert bank_result['stdout']['sha256'] == '6f1e114a35da29dcc593cbeeffe4888e811f3493e4187c09472f470395bb4afc'
assert set(audits).isdisjoint(bank_reports) and not any(row[0] == 'TransferBankRecovery' for row in records)
audits.update(bank_reports)
records.append(('TransferBankRecovery', bank['source'], bank_result['objects'][0]))
inputs += [pin(legacy / name) for name in ['plan.json', 'execute_bounded.py', 'events.jsonl', 'source-mapping.json', 'prepare.py', 'review.json']]
inputs += [bank['source'], bank_result['objects'][0], pin(bank_stdout)]
"""
s=s.replace(anchor,extra+anchor)
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Model composition of actual-source PermanentWriter participant/commit/capacity order with independently qualified original BankRecovery10, reused once with original source/object/full type/axiom reports and shared Readback17 unchanged. Recovery environment denotes independently observed store at completion invocation. Completion callback reports recovery returned error status; completed source participants derive clean recovery, ready/current roots/exact frozen boundary/16 roots/retained-history validity and independently observed partition health. Whole returned source commit derives same Ready owner/returned boundary and observed recovered store boundary/roots. Capacity error preserves Ready/new boundary and completed recovery; failed recovery prevents participant completion and blocks owner API status. Six fresh reports (two program definitions, four proofs), 570 original inherited reports/57 owned modules, strict finite/physical guards unchanged. Native prior participant-to-recovery state threading, current poison snapshots/intermediate readers, source complete/recovery/rollback/partition frames, locks/owner/Clone/typed values/physical I/O/durability remain explicit correspondence obligations; original recovery model is not relabeled native proof. No native/control/full Transfer certification or inferred healthy partitions/error rollback.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Original BankRecovery10 is an independently qualified model of recovery controls/observed roots/history/health; exact legacy source/object/reports reused, no imported replay and no duplicate Readback reports. Adapter only maps modeled returned recovery error to source writer completion callback success. Supplied store denotes recovery invocation observation, not defined to equal desired participant state; native state threading/same lock/partition poison snapshots/rollback-other-partition frames and durable I/O remain separate obligations. Recovery clean establishes ready/roots/boundary/history while partition health stays independently observed healthyAfter. Post-completion capacity error preserves source owner Ready and modeled observed recovery without rollback inference.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_AUTHENTICATED_BOUNDARY_ROOT_KEY_PROOFS_READER_HEIGHT_AND_VALUE_COHERENCE','SOURCE_WRITER_COMPLETION_ORIGINAL_RECOVERY_MODEL_JOIN')
s=s.replace('AUTHENTICATED_BOUNDARY_SOURCE_COMPLETE_FIFTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WRITER_RECOVERY_JOIN_COMPLETE_FIFTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 9, 'inherited_audits': 551", "'fresh_audits': 6, 'inherited_audits': 570")
s=s.replace('complete fifty-five-module owned root','complete fifty-seven-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source-writer/qualified-recovery model composition; original BankRecovery10 object/reports selected once with exact shared Readback identity and no replay. Native state threading/health/ownership/refinement remain explicit. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':6,'inherited_audits':570,'owned_modules':57,'BankRecovery_replay':False,'shared_Readback_duplicate':False})
