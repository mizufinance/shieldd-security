"""Seal retained staged nullifier encoding and exact source/axiom ancestry."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-whole-nullifier-admission-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-whole-nullifier-admission-20261011-01'", "CURRENT = DIAG / 'transfer-pending-nullifier-retention-20261011-02'")
s=s.replace('transfer-whole-nullifier-admission-checkpoint-20261011-01','transfer-pending-nullifier-retention-checkpoint-20261011-02')
s=s.replace('whole-nullifier-admission-endpoint','pending-nullifier-retention-endpoint')
replace("MODULE = 'TransferWholeNullifierAdmission01'", "MODULE = 'TransferPendingNullifierRetention01'")
replace('assert len(fresh) == 6','assert len(fresh) == 11')
replace("assert pool['objects'] == 32 and len(pool['inherited_public_reports']) == 319", "assert pool['objects'] == 33 and len(pool['inherited_public_reports']) == 325")
replace("manager_endpoint = DIAG / 'transfer-deferred-body-failure-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-whole-nullifier-admission-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-deferred-body-failure-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-whole-nullifier-admission-endpoint01.tar.xz'")
replace('1c2258413fcceaeb39e9eb935481c343f72c743e70c6354aabebea34cd74baf3','a11c8a379c40926862e3f3a341078a1ff2f68b4673e5663bd8e3383a52bf9b2f')
replace("tar.extractfile('reports/fresh-4-complete-declarations.txt')", "tar.extractfile('reports/fresh-6-complete-declarations.txt')")
replace('assert len(manager_reports) == 4','assert len(manager_reports) == 6')
replace("'module': 'TransferDeferredBodyFailure01'", "'module': 'TransferWholeNullifierAdmission01'")
replace('assert len(combined_reports) == 319','assert len(combined_reports) == 325')
replace('assert len(manager_selected) == 32','assert len(manager_selected) == 33')
replace("reference = {'deferred_body_failure':", "reference = {'whole_nullifier_admission':")
replace("'imported_complete_reports': 4", "'imported_complete_reports': 6")
replace("'complete_owned_modules': 32, 'inherited_complete_reports': 319", "'complete_owned_modules': 33, 'inherited_complete_reports': 325")
replace('Exact thirty-two-module closure through both complete-Item body contexts and source-order primitive/index/delivery/deferred joins, with all 319 inherited complete reports.', 'Exact thirty-three-module closure through whole action all-input admission and both complete-Item body/index/deferred branches, with all 325 inherited complete reports.')
replace("add(stdout, 'reports/fresh-6-complete-declarations.txt'", "add(stdout, 'reports/fresh-11-complete-declarations.txt'")
s=s.replace('installed source backend definition and five complete branch/reshape/whole nullifier admission proofs','eleven finite source object-footprint and whole-delivery retained encoding proofs')
s=s.replace('complete thirty-two-module first import root','complete thirty-three-module first import root')
s=s.replace('verified 319 inherited reports','verified 325 inherited reports')
s=s.replace('WHOLE_TRANSFER_DELIVERY_DERIVES_ALL_INPUT_NULLIFIER_ADMISSION_QUALIFIED','WHOLE_TRANSFER_DELIVERY_RETAINS_ADMITTED_PENDING_NULLIFIER_ENCODING_QUALIFIED')
replace("'fresh_definition_audits': 1", "'fresh_definition_audits': 0")
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 11")
replace("'fresh_complete_public_audits': 6", "'fresh_complete_public_audits': 11")
replace("'inherited_complete_public_audits': 319", "'inherited_complete_public_audits': 325")
replace("'rejected_attempts': 0", "'rejected_attempts': 1, 'rejected_preparation_attempts': 1")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"""    'scope': mapping['scope'] + ' All eleven handwritten theorem contracts have complete original type/axiom reports. The encoded value is the same inspected pending vector retained through arbitrary later note/SCT operations, Ordinary volume insertion and every index mode. Source key inequalities are explicit until a namespace/byte projection join; this does not assert actual Rust persistent-object alias isolation or durable publication. The failed whole attempt and stopped pre-admission preparation retain zero credit; all eleven contracts are unchanged.'}
""".rstrip()+s[end:]
s=s.replace("'fresh_audits': 6, 'inherited_audits': 319", "'fresh_audits': 11, 'inherited_audits': 325")
needle="add(ROOT / 'review.json', 'review.json'"
assert s.count(needle)==1
history="""rejected = DIAG / 'transfer-pending-nullifier-retention-20261011-01'
failed_events = [json.loads(line) for line in (rejected / 'events.jsonl').read_text().splitlines()]
assert len(failed_events) == 2 and failed_events[-1]['result']['status'] == 'failed'
for name in ['prepare-rejected-source-association.py', 'prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
             'source-mapping.json', 'events.jsonl', 'handwritten/TransferPendingNullifierRetention01.lean',
             'project/ShielddSecurity/TransferPendingNullifierRetention01.lean', 'runs/01-TransferPendingNullifierRetention01/stdout.txt']:
    add(rejected / name, 'rejected-predecessor/' + name, 'immutable rejected whole attempt and stopped pre-admission recipe; zero proof/control credit')
import re
def contracts(text):
    return {match.group(1): match.group(0).split(' :=', 1)[0] for match in re.finditer(
        r'^theorem (\\w+)[\\s\\S]*?(?=\\ntheorem|\\nset_option pp.all|\\Z)', text, re.M)}
original = (rejected / ('handwritten/' + MODULE + '.lean')).read_text()
successor = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
assert contracts(original) == contracts(successor) and len(contracts(original)) == 11
"""
s=s.replace(needle,history+needle)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':11,'inherited_reports':325,'owned_modules':33,'rejected_credit':0})
