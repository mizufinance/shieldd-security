"""Seal finite whole-delivery block sequence with complete exact ancestry."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-whole-reader-refusal-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-whole-reader-refusal-20261011-01'", "CURRENT = DIAG / 'transfer-block-pending-sequence-20261011-01'")
s=s.replace('transfer-whole-reader-refusal-checkpoint-20261011-01','transfer-block-pending-sequence-checkpoint-20261011-01')
s=s.replace('whole-reader-refusal-endpoint','block-pending-sequence-endpoint')
replace("MODULE = 'TransferWholeReaderRefusal01'", "MODULE = 'TransferBlockPendingSequence01'")
replace('assert len(fresh) == 9','assert len(fresh) == 10')
replace("assert pool['objects'] == 39 and len(pool['inherited_public_reports']) == 386", "assert pool['objects'] == 41 and len(pool['inherited_public_reports']) == 402")
replace("manager_endpoint = DIAG / 'transfer-nullifier-consensus-limits-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-pending-set-invariant-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-nullifier-consensus-limits-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-pending-set-invariant-endpoint01.tar.xz'")
replace('024022f5953fa854486c6ee2df48d045ca79126699e1a836b429f3f79b87aea5','d9311b43c7b2fc91b2cedf2ba9eb62b6d9021059d5bb5e571dbeb0468081508f')
replace("'module': 'TransferNullifierConsensusLimits01'", "'module': 'TransferPendingSetInvariant01'")
replace('assert len(combined_reports) == 386','assert len(combined_reports) == 402')
replace('assert len(manager_selected) == 39','assert len(manager_selected) == 41')
replace("reference = {'nullifier_consensus_limits':", "reference = {'pending_set_invariant':")
replace("'complete_owned_modules': 39, 'inherited_complete_reports': 386", "'complete_owned_modules': 41, 'inherited_complete_reports': 402")
s=s.replace('Exact thirty-nine-module closure through source consensus-capacity/current typed Reader/verified status, pending retention/replay and both complete body/index/deferred contexts, with 386 inherited complete reports; Readback seventeen reports included once.', 'Exact forty-one-module whole/current pending/durable reader/source capacity/list invariant closure, with 402 original inherited complete reports; shared StateDelta and seventeen Readback reports included once.')
replace("add(stdout, 'reports/fresh-9-complete-declarations.txt'", "add(stdout, 'reports/fresh-10-complete-declarations.txt'")
s=s.replace('explicit argument bundle, exact full delivery program and five observable whole reader refusal/parent queue preservation contracts','current parent pending/static-key whole binding/request/full step/finite walk/input concatenation and four invariant/global block theorems')
s=s.replace('complete thirty-nine-module first import root','complete forty-one-module first import root')
s=s.replace('verified 386 inherited reports','verified 402 inherited reports')
s=s.replace('WHOLE_TRANSFER_OBSERVABLE_READER_FAILURE_OR_AUTHENTICATED_SPENT_REFUSAL_PRESERVES_PARENT_QUEUE_QUALIFIED','WHOLE_TRANSFER_BLOCK_SEQUENCE_DERIVES_GLOBAL_DISTINCT_BOUNDED_PENDING_MEMBERSHIP_QUALIFIED')
replace("'fresh_definition_audits': 2", "'fresh_definition_audits': 6")
replace("'fresh_theorem_audits': 7", "'fresh_theorem_audits': 4")
replace("'fresh_complete_public_audits': 9", "'fresh_complete_public_audits': 10")
replace("'inherited_complete_public_audits': 386", "'inherited_complete_public_audits': 402")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All six definitions/request type and four theorems have complete original type/axiom reports. Symbolic sequence success derives every whole-step pending invariant and exact accumulated input order. Actual starting pending-object absence derives empty invariants; all global uniqueness/membership/capacity follow without desired intermediate-state assumptions. Native schedule/event/Host/durability correspondence remains open; no native/control/full certification credit.'}"+s[end:]
s=s.replace("'fresh_audits': 9, 'inherited_audits': 386", "'fresh_audits': 10, 'inherited_audits': 402")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':10,'inherited_reports':402,'owned_modules':41})
