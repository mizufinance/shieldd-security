"""Seal conditional captured-initial recovery bridge and retain zero-credit attempts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-stateful-participant-recovery-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-stateful-participant-recovery-20261011-01'", "CURRENT = DIAG / 'transfer-captured-recovery-20261011-04'")
s=s.replace('transfer-stateful-participant-recovery-checkpoint-20261011-01','transfer-captured-recovery-checkpoint-20261011-04')
s=s.replace('stateful-participant-recovery-endpoint','captured-recovery-endpoint')
replace("MODULE = 'TransferStatefulParticipantRecovery01'", "MODULE = 'TransferCapturedRecovery01'")
replace('assert len(fresh) == 17','assert len(fresh) == 8')
replace("assert pool['objects'] == 61 and len(pool['inherited_public_reports']) == 605", "assert pool['objects'] == 62 and len(pool['inherited_public_reports']) == 622")
replace("manager_endpoint = DIAG / 'transfer-stateful-store-commit-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-stateful-participant-recovery-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-stateful-store-commit-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-stateful-participant-recovery-endpoint01.tar.xz'")
replace('2bfb5fe995562ba7a86d69500a9705c8ed0c278a9da20707217eeeb0d3e7a351','c90e04e846b9929d61f0028b6d7873ea53dc6168238c3eea2154e95b9838d203')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-17-complete-declarations.txt')")
replace('assert len(manager_reports) == 13','assert len(manager_reports) == 17')
replace("'module': 'TransferStatefulStoreCommit01'", "'module': 'TransferStatefulParticipantRecovery01'")
replace('assert len(combined_reports) == 605','assert len(combined_reports) == 622')
replace('assert len(manager_selected) == 61','assert len(manager_selected) == 62')
replace("reference = {'stateful_store_commit':", "reference = {'stateful_participant_recovery':")
replace("'imported_complete_reports': 13", "'imported_complete_reports': 17")
replace("'complete_owned_modules': 61, 'inherited_complete_reports': 605", "'complete_owned_modules': 62, 'inherited_complete_reports': 622")
s=s.replace('Exact sixty-one-module','Exact sixty-two-module').replace('with 605 original inherited','with 622 original inherited')
replace("add(stdout, 'reports/fresh-17-complete-declarations.txt'", "add(stdout, 'reports/fresh-8-complete-declarations.txt'")
s=s.replace('actual temporal nullifier/application/lock/recovery input chain definitions and four participant/failure/capacity proofs','source captured-initial rollback selection/prepare/recovery and explicit forward partition frame contract with four conditional equivalence/failure proofs')
s=s.replace('complete sixty-one-module first import root','complete sixty-two-module first import root').replace('verified 605 inherited reports','verified 622 inherited reports')
s=s.replace('SOURCE_STATEFUL_PARTICIPANT_APPLICATION_COMPLETION_RECOVERY_INPUT_CHAIN_QUALIFIED','SOURCE_CAPTURED_INITIAL_RECOVERY_SELECTION_EXPLICIT_FORWARD_PARTITION_FRAME_BRIDGE_QUALIFIED')
replace("'fresh_definition_audits': 13", "'fresh_definition_audits': 4")
replace("'fresh_complete_public_audits': 17", "'fresh_complete_public_audits': 8")
replace("'inherited_complete_public_audits': 605", "'inherited_complete_public_audits': 622")
assert s.count("'fresh_audits': 17, 'inherited_audits': 605")==2
s=s.replace("'fresh_audits': 17, 'inherited_audits': 605", "'fresh_audits': 8, 'inherited_audits': 622")
replace("'rejected_attempts': 0", "'rejected_attempts': 2, 'withdrawn_unrun_attempts': 1")
anchor="add(stdout, 'reports/fresh-8-complete-declarations.txt'"
i=s.index(anchor)
extra="""for number in ['01','03']:
    rejected = DIAG / ('transfer-captured-recovery-20261011-'+number)
    rejected_events = [json.loads(line) for line in (rejected/'events.jsonl').read_text().splitlines()]
    assert len(rejected_events)==2 and rejected_events[-1]['result']['status']=='failed'
    for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCapturedRecovery01.lean','project/ShielddSecurity/TransferCapturedRecovery01.lean','runs/01-TransferCapturedRecovery01/stdout.txt']:
        assert pin(rejected/name) in plan['pins']
        add(rejected/name, 'rejected/attempt'+number+'/'+name, 'strict whole failed attempt; zero proof/control credit')
withdrawn = DIAG/'transfer-captured-recovery-20261011-02'
assert not (withdrawn/'events.jsonl').exists()
for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferCapturedRecovery01.lean','project/ShielddSecurity/TransferCapturedRecovery01.lean']:
    assert pin(withdrawn/name) in plan['pins']
    add(withdrawn/name, 'withdrawn-unrun/attempt02/'+name, 'prepared but never executed, withdrawn before launch; zero credit')
identity = json.loads((CURRENT/'rejected-object-identity.json').read_text())
assert identity['proof_credit']==0 and identity['imported'] is False
assert pin(identity['object']['path'])==identity['object'] and identity['object'] not in plan['owned_imports']
add(CURRENT/'rejected-object-identity.json', 'rejected/attempt03/object-identity.json', 'warning-only rejected object retained, never imported; identity metadata only, no object bytes')
"""
s=s[:i]+extra+s[i:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All eight declarations retain full original type/axiom reports. Whole 01 compiler failure and 03 unused-simp warning earn zero credit; prepared 02 never executed. Only induction/final equality tactics repaired; definitions/contracts and native forward-frame premise unchanged. Rejected object retained unused, no object bytes. Native frames/observations/ownership/IO/library/OS interfaces remain explicit. Zero native/control/full certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':622,'owned_modules':62,'rejected_attempts':2,'withdrawn02':'UNRUN'})
