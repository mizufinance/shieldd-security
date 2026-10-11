"""Seal exact ordinary pipeline/rollback reports with retained failure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-writer-recover-current-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-writer-recover-current-20261011-02'", "CURRENT = DIAG / 'transfer-end-to-end-20261011-02'")
s=s.replace('transfer-writer-recover-current-checkpoint-20261011-02','transfer-end-to-end-checkpoint-20261011-02').replace('writer-recover-current-endpoint','end-to-end-endpoint')
replace("MODULE = 'TransferWriterRecoverCurrent01'", "MODULE = 'TransferEndToEnd01'")
replace("assert pool['objects'] == 67 and len(pool['inherited_public_reports']) == 670", "assert pool['objects'] == 68 and len(pool['inherited_public_reports']) == 683")
replace("manager_endpoint = DIAG / 'transfer-host-seal-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-writer-recover-current-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-host-seal-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-writer-recover-current-endpoint01.tar.xz'")
replace('24e74ee89b5c60a100429615c34afccc996cdb83a223dc1f1b04761256120342','9f7dea8c9dda9be492c5c6a5d38677e825821571c9b7f1f0389858958d96557b')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-13-complete-declarations.txt')")
replace('assert len(manager_reports) == 7','assert len(manager_reports) == 13')
replace("'module': 'TransferHostSeal01'", "'module': 'TransferWriterRecoverCurrent01'")
replace('assert len(combined_reports) == 670','assert len(combined_reports) == 683')
replace('assert len(manager_selected) == 67','assert len(manager_selected) == 68')
replace("reference = {'host_seal':", "reference = {'writer_current_recovery':")
replace("'imported_complete_reports': 7", "'imported_complete_reports': 13")
replace("'complete_owned_modules': 67, 'inherited_complete_reports': 670", "'complete_owned_modules': 68, 'inherited_complete_reports': 683")
s=s.replace('sixty-seven-module','sixty-eight-module').replace('670 original inherited','683 original inherited').replace('verified 670 inherited','verified 683 inherited')
replace("rejected = DIAG/'transfer-writer-recover-current-20261011-01'", "rejected = DIAG/'transfer-end-to-end-20261011-01'")
s=s.replace('TransferWriterRecoverCurrent01.lean','TransferEndToEnd01.lean').replace('runs/01-TransferWriterRecoverCurrent01/stdout.txt','runs/01-TransferEndToEnd01/stdout.txt')
replace("'inherited_complete_public_audits': 670", "'inherited_complete_public_audits': 683")
replace("'fresh_audits': 13, 'inherited_audits': 670", "'fresh_audits': 13, 'inherited_audits': 683",2)
replace('SOURCE_WRITER_RECOVER_CURRENT_ACTUAL_SNAPSHOT_LOCK_AND_CAPTURED_PHYSICAL_RECOVERY_QUALIFIED','SOURCE_COMPOSED_ORDINARY_TRANSFER_PIPELINE_AND_ACTUAL_HOST_ROLLBACK_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All thirteen complete raw type/axiom reports retained. Whole strict failed 01 zero credit; three case-rewritten proof receipts repaired only, all definitions/premises/conclusions unchanged. Source no sorry/admit/axioms, accepted no sorryAx. Composed ordinary pipeline preserves actual temporal Stores; native captured-initial equivalence conditional on full partition frame contract. Native/finite/locks/filesystem/ownership/snapshot/ICS23 representation remain interfaces. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':13,'inherited_reports':683,'owned_modules':68,'rejected_attempts':1})
