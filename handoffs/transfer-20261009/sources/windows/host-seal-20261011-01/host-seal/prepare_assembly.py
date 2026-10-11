"""Seal Host same-Frozen phase/physical observation join and strict failed receipt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-host-end-block-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-host-end-block-20261011-01'", "CURRENT = DIAG / 'transfer-host-seal-20261011-02'")
s=s.replace('transfer-host-end-block-checkpoint-20261011-01','transfer-host-seal-checkpoint-20261011-02')
s=s.replace('host-end-block-endpoint','host-seal-endpoint')
replace("MODULE = 'TransferHostEndBlock01'", "MODULE = 'TransferHostSeal01'")
replace('assert len(fresh) == 10','assert len(fresh) == 7')
replace("assert pool['objects'] == 65 and len(pool['inherited_public_reports']) == 653", "assert pool['objects'] == 66 and len(pool['inherited_public_reports']) == 663")
replace("manager_endpoint = DIAG / 'transfer-host-sealed-commit-endpoint-20261011-04'", "manager_endpoint = DIAG / 'transfer-host-end-block-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-host-sealed-commit-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-host-end-block-endpoint01.tar.xz'")
replace('bd3a90d8a05d69ff4be8b8e0376d37740c06f90896680ee7b3faf3344d3b2611','24d02c04434606de3c907a02b46073c4e53b28950bad615dc09594095fadc526')
replace("tar.extractfile('reports/fresh-12-complete-declarations.txt')", "tar.extractfile('reports/fresh-10-complete-declarations.txt')")
replace('assert len(manager_reports) == 12','assert len(manager_reports) == 10')
replace("'module': 'TransferHostSealedCommit01'", "'module': 'TransferHostEndBlock01'")
replace('assert len(combined_reports) == 653','assert len(combined_reports) == 663')
replace('assert len(manager_selected) == 65','assert len(manager_selected) == 66')
replace("reference = {'host_sealed_commit':", "reference = {'host_end_block':")
replace("'imported_complete_reports': 12", "'imported_complete_reports': 10")
replace("'complete_owned_modules': 65, 'inherited_complete_reports': 653", "'complete_owned_modules': 66, 'inherited_complete_reports': 663")
s=s.replace('Exact sixty-five-module','Exact sixty-six-module').replace('with 653 original inherited','with 663 original inherited')
replace("add(stdout, 'reports/fresh-10-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
s=s.replace('source Host actual finalized state/queue/event transfer and prepared pending order with four success/refusal/progress proofs','Host seal source phase/actual writer/physical observation and same-Frozen actual transferred pending input join')
s=s.replace('complete sixty-five-module first import root','complete sixty-six-module first import root').replace('verified 653 inherited reports','verified 663 inherited reports')
s=s.replace('SOURCE_HOST_END_BLOCK_ACTUAL_FINALIZED_TRANSFER_PENDING_VECTOR_AND_PREPARED_OWNER_QUALIFIED','SOURCE_HOST_SEAL_INTERRUPTION_ACTUAL_INTENT_SAME_FROZEN_AND_OBSERVED_STORE_QUALIFIED')
replace("'fresh_definition_audits': 6", "'fresh_definition_audits': 3")
replace("'fresh_complete_public_audits': 10", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 653", "'inherited_complete_public_audits': 663")
assert s.count("'fresh_audits': 10, 'inherited_audits': 653")==2
s=s.replace("'fresh_audits': 10, 'inherited_audits': 653", "'fresh_audits': 7, 'inherited_audits': 663")
replace("'rejected_attempts': 0", "'rejected_attempts': 1")
anchor="add(stdout, 'reports/fresh-7-complete-declarations.txt'";i=s.index(anchor)
extra="""rejected = DIAG/'transfer-host-seal-20261011-01'
rejected_events = [json.loads(line) for line in (rejected/'events.jsonl').read_text().splitlines()]
assert len(rejected_events)==2 and rejected_events[-1]['result']['status']=='failed'
for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferHostSeal01.lean','project/ShielddSecurity/TransferHostSeal01.lean','runs/01-TransferHostSeal01/stdout.txt']:
    assert pin(rejected/name) in plan['pins']
    add(rejected/name, 'rejected/attempt01/'+name, 'whole strict parse failure from reserved field seal and compiler placeholders; zero credit')
"""
s=s[:i]+extra+s[i:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All seven declarations retain full original type/axiom reports. Whole strict failed 01 zero credit; reserved field seal renamed backend consistently with intended actual call/contracts unchanged. Source has no sorry/admit/axioms and accepted audits no sorryAx. Current Store after seal is independently observed, not assumed ready/healthy/durable. Native temporal/locks/filesystem/ownership/representation remain explicit. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':663,'owned_modules':66,'rejected_attempts':1})
