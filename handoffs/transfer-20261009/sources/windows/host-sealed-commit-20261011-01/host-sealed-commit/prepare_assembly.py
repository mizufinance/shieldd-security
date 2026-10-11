"""Seal ordinary Host commit and retain all zero-credit strict failed attempts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-stateful-participant-recovery-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-stateful-participant-recovery-20261011-01'", "CURRENT = DIAG / 'transfer-host-sealed-commit-20261011-04'")
s=s.replace('transfer-stateful-participant-recovery-checkpoint-20261011-01','transfer-host-sealed-commit-checkpoint-20261011-04')
s=s.replace('stateful-participant-recovery-endpoint','host-sealed-commit-endpoint')
replace("MODULE = 'TransferStatefulParticipantRecovery01'", "MODULE = 'TransferHostSealedCommit01'")
replace('assert len(fresh) == 17','assert len(fresh) == 12')
replace("assert pool['objects'] == 61 and len(pool['inherited_public_reports']) == 605", "assert pool['objects'] == 64 and len(pool['inherited_public_reports']) == 641")
replace("manager_endpoint = DIAG / 'transfer-stateful-store-commit-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-take-commit-state-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-stateful-store-commit-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-take-commit-state-endpoint01.tar.xz'")
replace('2bfb5fe995562ba7a86d69500a9705c8ed0c278a9da20707217eeeb0d3e7a351','483d2e20d0dcfc6302302f81e520aa2b0a74eb6806c3d1a4afbad6c18b065284')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-11-complete-declarations.txt')")
replace('assert len(manager_reports) == 13','assert len(manager_reports) == 11')
replace("'module': 'TransferStatefulStoreCommit01'", "'module': 'TransferTakeCommitState01'")
replace('assert len(combined_reports) == 605','assert len(combined_reports) == 641')
replace('assert len(manager_selected) == 61','assert len(manager_selected) == 64')
replace("reference = {'stateful_store_commit':", "reference = {'take_commit_state':")
replace("'imported_complete_reports': 13", "'imported_complete_reports': 11")
replace("'complete_owned_modules': 61, 'inherited_complete_reports': 605", "'complete_owned_modules': 64, 'inherited_complete_reports': 641")
s=s.replace('Exact sixty-one-module','Exact sixty-four-module').replace('with 605 original inherited','with 641 original inherited')
replace("add(stdout, 'reports/fresh-17-complete-declarations.txt'", "add(stdout, 'reports/fresh-12-complete-declarations.txt'")
s=s.replace('actual temporal nullifier/application/lock/recovery input chain definitions and four participant/failure/capacity proofs','ordinary Host sealed commit/actual reset and six source actual-writer/progress/capacity/root-presence proofs')
s=s.replace('complete sixty-one-module first import root','complete sixty-four-module first import root').replace('verified 605 inherited reports','verified 641 inherited reports')
s=s.replace('SOURCE_STATEFUL_PARTICIPANT_APPLICATION_COMPLETION_RECOVERY_INPUT_CHAIN_QUALIFIED','SOURCE_ORDINARY_HOST_SEALED_COMMIT_INTERRUPTION_ACTUAL_WRITER_AND_RESET_QUALIFIED')
replace("'fresh_definition_audits': 13", "'fresh_definition_audits': 6")
replace("'fresh_theorem_audits': 4", "'fresh_theorem_audits': 6")
replace("'fresh_complete_public_audits': 17", "'fresh_complete_public_audits': 12")
replace("'inherited_complete_public_audits': 605", "'inherited_complete_public_audits': 641")
assert s.count("'fresh_audits': 17, 'inherited_audits': 605")==2
s=s.replace("'fresh_audits': 17, 'inherited_audits': 605", "'fresh_audits': 12, 'inherited_audits': 641")
replace("'rejected_attempts': 0", "'rejected_attempts': 3")
anchor="add(stdout, 'reports/fresh-12-complete-declarations.txt'";i=s.index(anchor)
extra="""for number in ['01','02','03']:
    rejected = DIAG/('transfer-host-sealed-commit-20261011-'+number)
    rejected_events = [json.loads(line) for line in (rejected/'events.jsonl').read_text().splitlines()]
    assert len(rejected_events)==2 and rejected_events[-1]['result']['status']=='failed'
    for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferHostSealedCommit01.lean','project/ShielddSecurity/TransferHostSealedCommit01.lean','runs/01-TransferHostSealedCommit01/stdout.txt']:
        assert pin(rejected/name) in plan['pins']
        add(rejected/name, 'rejected/attempt'+number+'/'+name, 'strict whole failure and any compiler-generated placeholder earns zero credit; no handwritten sorry/axioms')
"""
s=s[:i]+extra+s[i:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All twelve declarations retain full original type/axiom reports. Whole failed 01/02/03 zero credit; record update layout and phase/reflexive proof tactics repaired with intended source program and theorem contracts unchanged. No source sorry/admit/axioms, and accepted audits have no sorryAx. Source root-presence derivation avoids vacuous missing-root negative-control claims. Genesis/native ownership/snapshot/library/OS interfaces remain explicit. Zero native/control/full certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':12,'inherited_reports':641,'owned_modules':64,'rejected_attempts':3})
