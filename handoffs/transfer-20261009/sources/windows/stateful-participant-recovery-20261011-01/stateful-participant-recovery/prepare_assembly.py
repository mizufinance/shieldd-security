"""Seal actual temporal participant-to-recovery input chain."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-stateful-store-commit-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-stateful-store-commit-20261011-02'", "CURRENT = DIAG / 'transfer-stateful-participant-recovery-20261011-01'")
s=s.replace('transfer-stateful-store-commit-checkpoint-20261011-02','transfer-stateful-participant-recovery-checkpoint-20261011-01')
s=s.replace('stateful-store-commit-endpoint','stateful-participant-recovery-endpoint')
replace("MODULE = 'TransferStatefulStoreCommit01'", "MODULE = 'TransferStatefulParticipantRecovery01'")
replace('assert len(fresh) == 13','assert len(fresh) == 17')
replace("assert pool['objects'] == 60 and len(pool['inherited_public_reports']) == 592", "assert pool['objects'] == 61 and len(pool['inherited_public_reports']) == 605")
replace("manager_endpoint = DIAG / 'transfer-record-read-bound-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-stateful-store-commit-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-record-read-bound-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-stateful-store-commit-endpoint01.tar.xz'")
replace('97a2fca49ce232a55c2fda07734a59258440ea3ddd571e4d3d3f2ca677c72cfe','2bfb5fe995562ba7a86d69500a9705c8ed0c278a9da20707217eeeb0d3e7a351')
replace("tar.extractfile('reports/fresh-8-complete-declarations.txt')", "tar.extractfile('reports/fresh-13-complete-declarations.txt')")
replace('assert len(manager_reports) == 8','assert len(manager_reports) == 13')
replace("'module': 'TransferRecordReadBound01'", "'module': 'TransferStatefulStoreCommit01'")
replace('assert len(combined_reports) == 592','assert len(combined_reports) == 605')
replace('assert len(manager_selected) == 60','assert len(manager_selected) == 61')
replace("reference = {'record_read_bound':", "reference = {'stateful_store_commit':")
replace("'imported_complete_reports': 8", "'imported_complete_reports': 13")
replace("'complete_owned_modules': 60, 'inherited_complete_reports': 592", "'complete_owned_modules': 61, 'inherited_complete_reports': 605")
s=s.replace('Exact sixty-module','Exact sixty-one-module').replace('with 592 original inherited','with 605 original inherited')
replace("add(stdout, 'reports/fresh-13-complete-declarations.txt'", "add(stdout, 'reports/fresh-17-complete-declarations.txt'")
s=s.replace('source stateful session/physical observation/commit definitions and five current-health/state-threaded/owned-frame proofs','actual temporal nullifier/application/lock/recovery input chain definitions and four participant/failure/capacity proofs')
s=s.replace('complete sixty-module first import root','complete sixty-one-module first import root').replace('verified 592 inherited reports','verified 605 inherited reports')
s=s.replace('SOURCE_STATEFUL_STORE_COMMIT_OBSERVED_ROOTS_CURRENT_POISON_AND_OWNED_FRAMES_QUALIFIED','SOURCE_STATEFUL_PARTICIPANT_APPLICATION_COMPLETION_RECOVERY_INPUT_CHAIN_QUALIFIED')
replace("'fresh_definition_audits': 8", "'fresh_definition_audits': 13")
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 4")
replace("'fresh_complete_public_audits': 13", "'fresh_complete_public_audits': 17")
replace("'inherited_complete_public_audits': 592", "'inherited_complete_public_audits': 605")
assert s.count("'fresh_audits': 13, 'inherited_audits': 592")==2
s=s.replace("'fresh_audits': 13, 'inherited_audits': 592", "'fresh_audits': 17, 'inherited_audits': 605")
replace("'rejected_attempts': 1", "'rejected_attempts': 0")
start=s.index("rejected = DIAG / 'transfer-stateful-store-commit-20261011-01'");end=s.index("add(stdout, 'reports/fresh-17-complete-declarations.txt'",start)
s=s[:start]+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All seventeen declarations retain full original type/axiom reports. Recovery invocation Store is exactly derived from prior actual participant physical observations; health remains independently observed, not inferred true. Native captured-initial-root recovery partition frames and temporal ghost/snapshot/ownership/Host/ICS23/OS correspondences remain explicit. Zero native/control/full certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':17,'inherited_reports':605,'owned_modules':61})
