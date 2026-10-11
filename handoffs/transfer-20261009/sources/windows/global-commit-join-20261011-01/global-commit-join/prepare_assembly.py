"""Seal whole input to publication join and complete finite field contract."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-end-to-end-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-end-to-end-20261011-02'", "CURRENT = DIAG / 'transfer-global-commit-join-20261011-01'")
s=s.replace('transfer-end-to-end-checkpoint-20261011-02','transfer-global-commit-join-checkpoint-20261011-01').replace('end-to-end-endpoint','global-commit-join-endpoint')
replace("MODULE = 'TransferEndToEnd01'", "MODULE = 'TransferGlobalCommitJoin01'")
replace('assert len(fresh) == 13','assert len(fresh) == 5')
replace("assert pool['objects'] == 68 and len(pool['inherited_public_reports']) == 683", "assert pool['objects'] == 69 and len(pool['inherited_public_reports']) == 696")
replace("manager_endpoint = DIAG / 'transfer-writer-recover-current-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-end-to-end-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-writer-recover-current-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-end-to-end-endpoint01.tar.xz'")
replace('9f7dea8c9dda9be492c5c6a5d38677e825821571c9b7f1f0389858958d96557b','7d38251e6c29af8105930c8f5d5ac46a3887ff3afa870d1a4e0d29cd03ad5eab')
replace("'module': 'TransferWriterRecoverCurrent01'", "'module': 'TransferEndToEnd01'")
replace('assert len(combined_reports) == 683','assert len(combined_reports) == 696')
replace('assert len(manager_selected) == 68','assert len(manager_selected) == 69')
replace("reference = {'writer_current_recovery':", "reference = {'end_to_end':")
replace("'complete_owned_modules': 68, 'inherited_complete_reports': 683", "'complete_owned_modules': 69, 'inherited_complete_reports': 696")
s=s.replace('sixty-eight-module','sixty-nine-module').replace('683 original inherited','696 original inherited').replace('verified 683 inherited','verified 696 inherited')
start=s.index("rejected = DIAG/");end=s.index("add(stdout,",start)
s=s[:start]+s[end:]
replace("add(stdout, 'reports/fresh-13-complete-declarations.txt'", "add(stdout, 'reports/fresh-5-complete-declarations.txt'")
replace("'fresh_definition_audits': 8", "'fresh_definition_audits': 2")
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 3")
replace("'fresh_complete_public_audits': 13", "'fresh_complete_public_audits': 5")
replace("'inherited_complete_public_audits': 683", "'inherited_complete_public_audits': 696")
replace("'fresh_audits': 13, 'inherited_audits': 683", "'fresh_audits': 5, 'inherited_audits': 696",2)
replace("'rejected_attempts': 1", "'rejected_attempts': 0")
replace('SOURCE_COMPOSED_ORDINARY_TRANSFER_PIPELINE_AND_ACTUAL_HOST_ROLLBACK_QUALIFIED','SOURCE_WHOLE_GLOBAL_INPUTS_TO_HOST_PUBLICATION_UNDER_FINITE_CODEC_AND_FINALIZATION_FIELD_CONTRACT_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All five complete original types/axioms include universal FinalizationPendingFrame; accepted no sorryAx. Concrete index and transfer frames derived without count or per-callback frames. Whole default walk to published ordinary commit exact global inputs proved under explicit finite codec/key/finalization field contracts. Native temporal/partition/finite/locks/filesystem/ownership/snapshot/ICS23 remain interfaces. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':5,'inherited_reports':696,'owned_modules':69,'rejected_attempts':0})
