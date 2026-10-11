"""Seal source sealed/concrete-flush/exclusive transfer with strict receipt retention."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-stateful-store-commit-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-stateful-store-commit-20261011-02'", "CURRENT = DIAG / 'transfer-take-commit-state-20261011-02'")
s=s.replace('transfer-stateful-store-commit-checkpoint-20261011-02','transfer-take-commit-state-checkpoint-20261011-02')
s=s.replace('stateful-store-commit-endpoint','take-commit-state-endpoint')
replace("MODULE = 'TransferStatefulStoreCommit01'", "MODULE = 'TransferTakeCommitState01'")
replace('assert len(fresh) == 13','assert len(fresh) == 11')
replace("assert pool['objects'] == 60 and len(pool['inherited_public_reports']) == 592", "assert pool['objects'] == 63 and len(pool['inherited_public_reports']) == 630")
replace("manager_endpoint = DIAG / 'transfer-record-read-bound-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-captured-recovery-endpoint-20261011-04'")
replace("manager_archive = manager_endpoint / 'portable-windows-record-read-bound-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-captured-recovery-endpoint01.tar.xz'")
replace('97a2fca49ce232a55c2fda07734a59258440ea3ddd571e4d3d3f2ca677c72cfe','4053ed4b65dc33cf05e6af617d9e07388ec9e70c1298221788a84e81214071d6')
replace("'module': 'TransferRecordReadBound01'", "'module': 'TransferCapturedRecovery01'")
replace('assert len(combined_reports) == 592','assert len(combined_reports) == 630')
replace('assert len(manager_selected) == 60','assert len(manager_selected) == 63')
replace("reference = {'record_read_bound':", "reference = {'captured_recovery':")
replace("'complete_owned_modules': 60, 'inherited_complete_reports': 592", "'complete_owned_modules': 63, 'inherited_complete_reports': 630")
s=s.replace('Exact sixty-module','Exact sixty-three-module').replace('with 592 original inherited','with 630 original inherited')
replace("add(stdout, 'reports/fresh-13-complete-declarations.txt'", "add(stdout, 'reports/fresh-11-complete-declarations.txt'")
s=s.replace('source stateful session/physical observation/commit definitions and five current-health/state-threaded/owned-frame proofs','source sealed/concrete flush/exclusive transfer/replacement and six derived transfer/restore/queue/object-frame proofs')
s=s.replace('complete sixty-module first import root','complete sixty-three-module first import root').replace('verified 592 inherited reports','verified 630 inherited reports')
s=s.replace('SOURCE_STATEFUL_STORE_COMMIT_OBSERVED_ROOTS_CURRENT_POISON_AND_OWNED_FRAMES_QUALIFIED','SOURCE_TAKE_COMMIT_STATE_SEALED_CONCRETE_FLUSH_EXCLUSIVE_TRANSFER_AND_REPLACEMENT_QUALIFIED')
replace("'fresh_definition_audits': 8", "'fresh_definition_audits': 5")
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 6")
replace("'fresh_complete_public_audits': 13", "'fresh_complete_public_audits': 11")
replace("'inherited_complete_public_audits': 592", "'inherited_complete_public_audits': 630")
assert s.count("'fresh_audits': 13, 'inherited_audits': 592")==2
s=s.replace("'fresh_audits': 13, 'inherited_audits': 592", "'fresh_audits': 11, 'inherited_audits': 630")
replace("rejected = DIAG / 'transfer-stateful-store-commit-20261011-01'", "rejected = DIAG / 'transfer-take-commit-state-20261011-01'")
replace("'handwritten/TransferStatefulStoreCommit01.lean','project/ShielddSecurity/TransferStatefulStoreCommit01.lean','runs/01-TransferStatefulStoreCommit01/stdout.txt'", "'handwritten/TransferTakeCommitState01.lean','project/ShielddSecurity/TransferTakeCommitState01.lean','runs/01-TransferTakeCommitState01/stdout.txt'")
s=s.replace('strict whole attempt failed due to frame induction proof tactic','strict whole compiled attempt failed due to constructor-name proof binder warning')
anchor="add(stdout, 'reports/fresh-11-complete-declarations.txt'";i=s.index(anchor)
extra="""identity = json.loads((CURRENT/'rejected-object-identity.json').read_text())
assert identity['proof_credit']==0 and identity['imported'] is False
assert pin(identity['object']['path'])==identity['object'] and identity['object'] not in plan['owned_imports']
add(CURRENT/'rejected-object-identity.json', 'rejected/attempt01/object-identity.json', 'warning-only rejected object retained, never imported; identity metadata only, no object bytes')
"""
s=s[:i]+extra+s[i:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All eleven declarations retain full original type/axiom reports. Warning-only compiled 01 earns zero credit and its object is retained unused; only proof binder renamed. Concrete flush index error preserves delivered parent and consumes queue; successful transfer retains post-flush pending objects, subject to original count observation and native representation/ownership interfaces. Zero native/control/full certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':11,'inherited_reports':630,'owned_modules':63,'rejected_attempts':1})
