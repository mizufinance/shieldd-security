"""Seal original BankRecovery reuse and source writer completion composition."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-authenticated-boundary-source-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-authenticated-boundary-source-20261011-01'", "CURRENT = DIAG / 'transfer-writer-recovery-join-20261011-01'")
s=s.replace('transfer-authenticated-boundary-source-checkpoint-20261011-01','transfer-writer-recovery-join-checkpoint-20261011-01')
s=s.replace('authenticated-boundary-source-endpoint','writer-recovery-join-endpoint')
replace("MODULE = 'TransferAuthenticatedBoundarySource01'", "MODULE = 'TransferWriterRecoveryJoin01'")
replace('assert len(fresh) == 9','assert len(fresh) == 6')
replace("assert pool['objects'] == 55 and len(pool['inherited_public_reports']) == 551", "assert pool['objects'] == 57 and len(pool['inherited_public_reports']) == 570")
replace("manager_endpoint = DIAG / 'transfer-boundary-reader-source-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-authenticated-boundary-source-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-boundary-reader-source-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-authenticated-boundary-source-endpoint01.tar.xz'")
replace('928eee7e3e07762fae8f6a8f496f8fe887d5b2d3ed371303e5c903a78c43a937','56d448763b1ca398393bd18d4249170924bc2dd56321f8558f8a41456908233c')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-9-complete-declarations.txt')")
replace('assert len(manager_reports) == 7','assert len(manager_reports) == 9')
replace("'module': 'TransferBoundaryReaderSource01'", "'module': 'TransferAuthenticatedBoundarySource01'")
replace('assert len(combined_reports) == 551','assert len(combined_reports) == 570')
replace('assert len(manager_selected) == 55','assert len(manager_selected) == 57')
anchor='assert len(combined_reports) == 570'; assert s.count(anchor)==1
extra="""legacy = DIAG / 'transfer-readback-recovery-publication-20261010-02'
legacy_endpoint = DIAG / 'transfer-readback-publication-endpoint-20261010-01'
legacy_archive = legacy_endpoint / 'portable-windows-readback-publication-endpoint01.tar.xz'
assert pin(legacy_archive)['sha256'] == '48b33b403223914e40cfedfd0d6031e68bde14fa5b659a72823caed344de47a8'
with tarfile.open(legacy_archive, 'r:xz') as tar:
    legacy_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    legacy_events = [json.loads(row) for row in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    bank_stdout = tar.extractfile('reports/TransferBankRecovery-complete-types-and-axioms.txt').read().decode()
    bank_source = tar.extractfile('source/ShielddSecurity/TransferBankRecovery.lean').read()
bank_target = next(row for row in legacy_plan['targets'] if row['module'] == 'TransferBankRecovery')
bank_result = next(row['result'] for row in legacy_events if row['event'] == 'attempt_finished' and row['module'] == 'TransferBankRecovery')
assert bank_result['status'] == 'passed'
bank_reports = m.audit(bank_stdout, bank_target['audit_names'])
assert len(bank_reports) == 10 and bank_reports == bank_result['audits']
assert bank_source == Path(bank_target['source']['path']).read_bytes()
assert bank_stdout.encode() == Path(bank_result['stdout']['path']).read_bytes()
shared_target = next(row for row in legacy_plan['targets'] if row['module'] == 'TransferReadback')
shared_result = next(row['result'] for row in legacy_events if row['event'] == 'attempt_finished' and row['module'] == 'TransferReadback')
shared_selected = next(row for row in manager_selected if row['module'] == 'TransferReadback')
assert shared_selected['source'] == shared_target['source'] and shared_selected['object'] == shared_result['objects'][0]
assert {name: combined_reports[name] for name in shared_target['audit_names']} == shared_result['audits']
assert set(combined_reports).isdisjoint(bank_reports)
combined_reports.update(bank_reports)
manager_selected.append({'module':'TransferBankRecovery','source':bank_target['source'],'object':bank_result['objects'][0]})
"""
s=s.replace(anchor,extra+anchor)
replace('carriers = [pin(manager_archive)]','carriers = [pin(manager_archive), pin(legacy_archive)]')
replace("reference = {'boundary_reader_source':", "reference = {'authenticated_boundary_source':")
replace("'imported_complete_reports': 7", "'imported_complete_reports': 9")
replace("'ancestors': manager_reference, 'complete_owned_modules': 55, 'inherited_complete_reports': 551,", "'ancestors': manager_reference, 'original_bank_recovery': {'archive':pin(legacy_archive), 'manifest':pin(legacy_endpoint / 'manifest.json'), 'selected_reports':10, 'source':bank_target['source'], 'object_identity':bank_result['objects'][0], 'shared_readback_17_reused_once':True, 'compiler_replay':False}, 'complete_owned_modules': 57, 'inherited_complete_reports': 570,")
s=s.replace('Exact fifty-five-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging/keys/reader/authenticated snapshot closure, with 551 original inherited complete reports', 'Exact fifty-seven-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging/keys/reader/authenticated snapshot/original recovery closure, with 570 original inherited complete reports; original BankRecovery10 imported without replay')
replace("add(stdout, 'reports/fresh-9-complete-declarations.txt'", "add(stdout, 'reports/fresh-6-complete-declarations.txt'")
s=s.replace('source snapshot/key authentication recurrence/actual boundary and height program definitions and four derived source call/value coherence proofs','source writer completion adapter to original qualified recovery model and four boundary/health/capacity/error composition proofs')
s=s.replace('complete fifty-five-module first import root','complete fifty-seven-module first import root')
s=s.replace('verified 551 inherited reports','verified 570 inherited reports')
s=s.replace('SOURCE_AUTHENTICATED_BOUNDARY_ROOT_KEY_PROOFS_READER_HEIGHT_AND_VALUE_COHERENCE_QUALIFIED','SOURCE_WRITER_COMPLETION_ORIGINAL_RECOVERY_MODEL_JOIN_QUALIFIED')
replace("'fresh_definition_audits': 5", "'fresh_definition_audits': 2")
replace("'fresh_complete_public_audits': 9", "'fresh_complete_public_audits': 6")
replace("'inherited_complete_public_audits': 551", "'inherited_complete_public_audits': 570")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All six fresh declarations and original BankRecovery10 have complete original type/axiom reports. Shared Readback17 is unchanged and selected once. Native temporal state threading/current poison snapshots/partition frames/locks/IO/durability remain explicit rather than inferred from modeled adapter success. Recovery health stays independently observed; zero native/control/full certification credit.'}"+s[end:]
s=s.replace("'fresh_audits': 9, 'inherited_audits': 551", "'fresh_audits': 6, 'inherited_audits': 570")
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"; assert s.count(anchor)==1
extra="""for name in ['plan.json', 'execute_bounded.py', 'events.jsonl', 'source-mapping.json', 'prepare.py', 'review.json', 'project/ShielddSecurity/TransferBankRecovery.lean', 'runs/02-TransferBankRecovery/stdout.txt']:
    add(legacy / name, 'original-BankRecovery/' + name, 'exact original independently qualified legacy source/runner/receipts/full reports; BankRecovery10 selected once, no replay or new native credit')
"""
s=s.replace(anchor,extra+anchor)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':570,'owned_modules':57,'BankRecovery_replayed':False})
