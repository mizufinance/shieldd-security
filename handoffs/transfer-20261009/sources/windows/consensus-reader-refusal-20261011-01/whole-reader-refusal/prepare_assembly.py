"""Seal complete whole reader refusal contracts and exact consensus ancestry."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-current-pending-replay-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-current-pending-replay-20261011-01'", "CURRENT = DIAG / 'transfer-whole-reader-refusal-20261011-01'")
s=s.replace('transfer-current-pending-replay-checkpoint-20261011-01','transfer-whole-reader-refusal-checkpoint-20261011-01')
s=s.replace('current-pending-replay-endpoint','whole-reader-refusal-endpoint')
replace("MODULE = 'TransferCurrentPendingReplay01'", "MODULE = 'TransferWholeReaderRefusal01'")
replace('assert len(fresh) == 8','assert len(fresh) == 9')
replace("assert pool['objects'] == 35 and len(pool['inherited_public_reports']) == 343", "assert pool['objects'] == 39 and len(pool['inherited_public_reports']) == 386")
replace("manager_endpoint = DIAG / 'transfer-nullifier-object-keys-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-nullifier-consensus-limits-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-nullifier-object-keys-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-nullifier-consensus-limits-endpoint01.tar.xz'")
replace('4596a11c227ab40856e24f331911de55ebb45b02719abd3b64b6eb195c873f79','024022f5953fa854486c6ee2df48d045ca79126699e1a836b429f3f79b87aea5')
replace("'module': 'TransferNullifierObjectKeys01'", "'module': 'TransferNullifierConsensusLimits01'")
replace('assert len(combined_reports) == 343','assert len(combined_reports) == 386')
replace('assert len(manager_selected) == 35','assert len(manager_selected) == 39')
replace("reference = {'nullifier_object_keys':", "reference = {'nullifier_consensus_limits':")
replace("'complete_owned_modules': 35, 'inherited_complete_reports': 343", "'complete_owned_modules': 39, 'inherited_complete_reports': 386")
s=s.replace('Exact thirty-five-module closure through source-derived object keys, retained pending encoding and both complete-Item body/index/deferred branches, with all 343 inherited complete reports.', 'Exact thirty-nine-module closure through source consensus-capacity/current typed Reader/verified status, pending retention/replay and both complete body/index/deferred contexts, with 386 inherited complete reports; Readback seventeen reports included once.')
replace("add(stdout, 'reports/fresh-8-complete-declarations.txt'", "add(stdout, 'reports/fresh-9-complete-declarations.txt'")
s=s.replace('current typed object getter and whole two-action shared-input replay refusal','explicit argument bundle, exact full delivery program and five observable whole reader refusal/parent queue preservation contracts')
s=s.replace('complete thirty-five-module first import root','complete thirty-nine-module first import root')
s=s.replace('verified 343 inherited reports','verified 386 inherited reports')
s=s.replace('CURRENT_TYPED_PENDING_READ_DERIVES_SHARED_INPUT_REPLAY_REFUSAL_QUALIFIED','WHOLE_TRANSFER_OBSERVABLE_READER_FAILURE_OR_AUTHENTICATED_SPENT_REFUSAL_PRESERVES_PARENT_QUEUE_QUALIFIED')
replace("'fresh_definition_audits': 3", "'fresh_definition_audits': 2")
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 7")
replace("'fresh_complete_public_audits': 8", "'fresh_complete_public_audits': 9")
replace("'inherited_complete_public_audits': 343", "'inherited_complete_public_audits': 386")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Argument bundle type, exact delivery definition and all seven theorems have complete original type/axiom reports. Success observation and finish refusal lemmas are reused symbolically. No primitive/body/index failure is assumed; native operational observations and Merkle soundness remain explicit interfaces. No executed semantic-control or full Transfer certification credit.'}"+s[end:]
s=s.replace("'fresh_audits': 8, 'inherited_audits': 343", "'fresh_audits': 9, 'inherited_audits': 386")
replace("add(ROOT / 'prepare_assembly-rejected-selector.py', 'preparation-stopped/prepare_assembly-rejected-selector.py', 'unexecuted sealer preparation selector rejected before assembler creation; zero proof or control credit')\n",'')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':9,'inherited_reports':386,'owned_modules':39})
