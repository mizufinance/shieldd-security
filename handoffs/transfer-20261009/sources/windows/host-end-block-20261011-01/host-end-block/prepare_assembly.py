"""Seal actual finalized transfer/pending prepare chain and explicit capstone plan."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-stateful-participant-recovery-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-stateful-participant-recovery-20261011-01'", "CURRENT = DIAG / 'transfer-host-end-block-20261011-01'")
s=s.replace('transfer-stateful-participant-recovery-checkpoint-20261011-01','transfer-host-end-block-checkpoint-20261011-01')
s=s.replace('stateful-participant-recovery-endpoint','host-end-block-endpoint')
replace("MODULE = 'TransferStatefulParticipantRecovery01'", "MODULE = 'TransferHostEndBlock01'")
replace('assert len(fresh) == 17','assert len(fresh) == 10')
replace("assert pool['objects'] == 61 and len(pool['inherited_public_reports']) == 605", "assert pool['objects'] == 65 and len(pool['inherited_public_reports']) == 653")
replace("manager_endpoint = DIAG / 'transfer-stateful-store-commit-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-host-sealed-commit-endpoint-20261011-04'")
replace("manager_archive = manager_endpoint / 'portable-windows-stateful-store-commit-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-host-sealed-commit-endpoint01.tar.xz'")
replace('2bfb5fe995562ba7a86d69500a9705c8ed0c278a9da20707217eeeb0d3e7a351','bd3a90d8a05d69ff4be8b8e0376d37740c06f90896680ee7b3faf3344d3b2611')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-12-complete-declarations.txt')")
replace('assert len(manager_reports) == 13','assert len(manager_reports) == 12')
replace("'module': 'TransferStatefulStoreCommit01'", "'module': 'TransferHostSealedCommit01'")
replace('assert len(combined_reports) == 605','assert len(combined_reports) == 653')
replace('assert len(manager_selected) == 61','assert len(manager_selected) == 65')
replace("reference = {'stateful_store_commit':", "reference = {'host_sealed_commit':")
replace("'imported_complete_reports': 13", "'imported_complete_reports': 12")
replace("'complete_owned_modules': 61, 'inherited_complete_reports': 605", "'complete_owned_modules': 65, 'inherited_complete_reports': 653")
s=s.replace('Exact sixty-one-module','Exact sixty-five-module').replace('with 605 original inherited','with 653 original inherited')
replace("add(stdout, 'reports/fresh-17-complete-declarations.txt'", "add(stdout, 'reports/fresh-10-complete-declarations.txt'")
s=s.replace('actual temporal nullifier/application/lock/recovery input chain definitions and four participant/failure/capacity proofs','source Host actual finalized state/queue/event transfer and prepared pending order with four success/refusal/progress proofs')
s=s.replace('complete sixty-one-module first import root','complete sixty-five-module first import root').replace('verified 605 inherited reports','verified 653 inherited reports')
s=s.replace('SOURCE_STATEFUL_PARTICIPANT_APPLICATION_COMPLETION_RECOVERY_INPUT_CHAIN_QUALIFIED','SOURCE_HOST_END_BLOCK_ACTUAL_FINALIZED_TRANSFER_PENDING_VECTOR_AND_PREPARED_OWNER_QUALIFIED')
replace("'fresh_definition_audits': 13", "'fresh_definition_audits': 6")
replace("'fresh_complete_public_audits': 17", "'fresh_complete_public_audits': 10")
replace("'inherited_complete_public_audits': 605", "'inherited_complete_public_audits': 653")
assert s.count("'fresh_audits': 17, 'inherited_audits': 605")==2
s=s.replace("'fresh_audits': 17, 'inherited_audits': 605", "'fresh_audits': 10, 'inherited_audits': 653")
anchor="add(stdout, 'reports/fresh-10-complete-declarations.txt'";i=s.index(anchor)
s=s[:i]+"capstone = DIAG/'transfer-capstone-plan-20261011-01/plan.json'\nassert pin(capstone) in plan['pins'] and pin(capstone)['sha256']=='d6ab4913d7b42c52b32357ac04bfc3da58b7b162140c2556bba90915d40ca067'\nadd(capstone, 'context/handwritten-capstone-plan.json', 'planning only: explicit native temporal/poison/snapshot/ICS23/library/Host/ownership/OS/full gate obligations; zero evidence credit')\n"+s[i:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All ten declarations retain full original type/axiom reports. Actual application returned state/queue/event observations feed concrete take_commit_state then actual pending ordered read and source writer preparation. Signed native height/component/SCT/epoch/Arc expect panic/ownership/library correspondence remains explicit. Handwritten capstone plan earns zero proof/evidence credit and full Transfer remains OPEN. Zero native/control/full certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':10,'inherited_reports':653,'owned_modules':65,'capstone_plan':'PLANNING_ONLY'})
