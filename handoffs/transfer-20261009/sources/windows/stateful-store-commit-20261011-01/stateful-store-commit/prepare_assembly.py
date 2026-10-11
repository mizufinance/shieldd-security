"""Seal current poison/root state threading and retain strict rejected attempt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-durable-write-source-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-durable-write-source-20261011-01'", "CURRENT = DIAG / 'transfer-stateful-store-commit-20261011-02'")
s=s.replace('transfer-durable-write-source-checkpoint-20261011-01','transfer-stateful-store-commit-checkpoint-20261011-02')
s=s.replace('durable-write-source-endpoint','stateful-store-commit-endpoint')
replace("MODULE = 'TransferDurableWriteSource01'", "MODULE = 'TransferStatefulStoreCommit01'")
replace('assert len(fresh) == 8','assert len(fresh) == 13')
replace("assert pool['objects'] == 58 and len(pool['inherited_public_reports']) == 576", "assert pool['objects'] == 60 and len(pool['inherited_public_reports']) == 592")
replace("manager_endpoint = DIAG / 'transfer-writer-recovery-join-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-record-read-bound-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-writer-recovery-join-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-record-read-bound-endpoint01.tar.xz'")
replace('334ccfbfa9bbf867f4ee909df762fbca06052f7cf641a992167bb6b74f418223','97a2fca49ce232a55c2fda07734a59258440ea3ddd571e4d3d3f2ca677c72cfe')
replace("tar.extractfile('reports/fresh-6-complete-declarations.txt')", "tar.extractfile('reports/fresh-8-complete-declarations.txt')")
replace('assert len(manager_reports) == 6','assert len(manager_reports) == 8')
replace("'module': 'TransferWriterRecoveryJoin01'", "'module': 'TransferRecordReadBound01'")
replace('assert len(combined_reports) == 576','assert len(combined_reports) == 592')
replace('assert len(manager_selected) == 58','assert len(manager_selected) == 60')
replace("reference = {'writer_recovery_join':", "reference = {'record_read_bound':")
replace("'imported_complete_reports': 6", "'imported_complete_reports': 8")
replace("'complete_owned_modules': 58, 'inherited_complete_reports': 576", "'complete_owned_modules': 60, 'inherited_complete_reports': 592")
s=s.replace('Exact fifty-eight-module','Exact sixty-module').replace('with 576 original inherited','with 592 original inherited')
replace("add(stdout, 'reports/fresh-8-complete-declarations.txt'", "add(stdout, 'reports/fresh-13-complete-declarations.txt'")
s=s.replace('source file operation observation/durable write/intent writer installation definitions and four source success/missing-parent/directory-failure/intent-refusal proofs','source stateful session/physical observation/commit definitions and five current-health/state-threaded/owned-frame proofs')
s=s.replace('complete fifty-eight-module first import root','complete sixty-module first import root').replace('verified 576 inherited reports','verified 592 inherited reports')
s=s.replace('SOURCE_DURABLE_FILE_WRITE_ORDER_OBSERVED_PROGRESS_AND_INTENT_FAILURE_QUALIFIED','SOURCE_STATEFUL_STORE_COMMIT_OBSERVED_ROOTS_CURRENT_POISON_AND_OWNED_FRAMES_QUALIFIED')
replace("'fresh_definition_audits': 4", "'fresh_definition_audits': 8")
replace("'fresh_theorem_audits': 4", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 8", "'fresh_complete_public_audits': 13")
replace("'inherited_complete_public_audits': 576", "'inherited_complete_public_audits': 592")
assert s.count("'fresh_audits': 8, 'inherited_audits': 576")==2
s=s.replace("'fresh_audits': 8, 'inherited_audits': 576", "'fresh_audits': 13, 'inherited_audits': 592")
replace("'rejected_attempts': 0", "'rejected_attempts': 1")
anchor="add(stdout, 'reports/fresh-13-complete-declarations.txt'"
i=s.index(anchor)
extra="""rejected = DIAG / 'transfer-stateful-store-commit-20261011-01'
rejected_events = [json.loads(line) for line in (rejected / 'events.jsonl').read_text().splitlines()]
assert len(rejected_events)==2 and rejected_events[-1]['result']['status']=='failed'
for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferStatefulStoreCommit01.lean','project/ShielddSecurity/TransferStatefulStoreCommit01.lean','runs/01-TransferStatefulStoreCommit01/stdout.txt']:
    assert pin(rejected/name) in plan['pins']
    add(rejected/name, 'rejected/attempt01/'+name, 'strict whole attempt failed due to frame induction proof tactic; zero proof/control credit')
"""
s=s[:i]+extra+s[i:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All thirteen declarations retain full original type/axiom reports. Rejected 01 retained whole with zero credit; only frame lemma induction tactic repaired, definitions/contracts unchanged. Physical callback observations are not native semantic correspondence or negative controls. Zero native/control/full certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':13,'inherited_reports':592,'owned_modules':60,'rejected_attempts':1})
