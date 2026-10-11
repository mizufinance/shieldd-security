"""Seal reusable list invariants and preparation-only stopped setup."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-whole-reader-refusal-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-whole-reader-refusal-20261011-01'", "CURRENT = DIAG / 'transfer-pending-set-invariant-20261011-02'")
s=s.replace('transfer-whole-reader-refusal-checkpoint-20261011-01','transfer-pending-set-invariant-checkpoint-20261011-02')
s=s.replace('whole-reader-refusal-endpoint','pending-set-invariant-endpoint')
replace("MODULE = 'TransferWholeReaderRefusal01'", "MODULE = 'TransferPendingSetInvariant01'")
replace('assert len(fresh) == 9','assert len(fresh) == 7')
replace("assert pool['objects'] == 39 and len(pool['inherited_public_reports']) == 386", "assert pool['objects'] == 40 and len(pool['inherited_public_reports']) == 395")
replace("manager_endpoint = DIAG / 'transfer-nullifier-consensus-limits-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-whole-reader-refusal-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-nullifier-consensus-limits-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-whole-reader-refusal-endpoint01.tar.xz'")
replace('024022f5953fa854486c6ee2df48d045ca79126699e1a836b429f3f79b87aea5','f2241e2546c2f3975d5f64f4f8d90a21e5a9d98b019e06c1a421b598fe27c85d')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-9-complete-declarations.txt')")
replace('assert len(manager_reports) == 7','assert len(manager_reports) == 9')
replace("'module': 'TransferNullifierConsensusLimits01'", "'module': 'TransferWholeReaderRefusal01'")
replace('assert len(combined_reports) == 386','assert len(combined_reports) == 395')
replace('assert len(manager_selected) == 39','assert len(manager_selected) == 40')
replace("reference = {'nullifier_consensus_limits':", "reference = {'whole_reader_refusal':")
replace("'imported_complete_reports': 7", "'imported_complete_reports': 9")
replace("'complete_owned_modules': 39, 'inherited_complete_reports': 386", "'complete_owned_modules': 40, 'inherited_complete_reports': 395")
s=s.replace('Exact thirty-nine-module closure through source consensus-capacity/current typed Reader/verified status, pending retention/replay and both complete body/index/deferred contexts, with 386 inherited complete reports; Readback seventeen reports included once.', 'Exact forty-module whole/current-pending/durable-reader/source-capacity/refusal closure, with 395 original inherited complete reports; shared StateDelta and seventeen Readback reports included once.')
replace("add(stdout, 'reports/fresh-9-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
s=s.replace('explicit argument bundle, exact full delivery program and five observable whole reader refusal/parent queue preservation contracts','two pending invariant predicates and five reusable finite symbolic set/list/inspection invariant lemmas')
s=s.replace('complete thirty-nine-module first import root','complete forty-module first import root')
s=s.replace('verified 386 inherited reports','verified 395 inherited reports')
s=s.replace('WHOLE_TRANSFER_OBSERVABLE_READER_FAILURE_OR_AUTHENTICATED_SPENT_REFUSAL_PRESERVES_PARENT_QUEUE_QUALIFIED','SYMBOLIC_PENDING_SET_ORDERED_VECTOR_COHERENCE_AND_DUPLICATE_FREE_APPEND_QUALIFIED')
replace("'fresh_theorem_audits': 7", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 9", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 386", "'inherited_complete_public_audits': 395")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Both predicates and all five reusable lemmas have complete original type/axiom reports. Initial typed collection correspondence remains explicit; admitted new invariants are derived symbolically from actual inspection success. No native/control/full certification credit.'}"+s[end:]
s=s.replace("'fresh_audits': 9, 'inherited_audits': 386", "'fresh_audits': 7, 'inherited_audits': 395")
needle="add(ROOT / 'review.json', 'review.json'"
assert s.count(needle)==1
history="""stopped = DIAG / 'transfer-pending-set-invariant-20261011-01'
assert not (stopped / 'plan.json').exists() and not (stopped / 'events.jsonl').exists()
assert not (stopped / ('project/ShielddSecurity/' + MODULE + '.olean')).exists()
assert (stopped / ('handwritten/' + MODULE + '.lean')).read_bytes() == (CURRENT / ('handwritten/' + MODULE + '.lean')).read_bytes()
for name in ['prepare_recipe.py', 'prepare.py', 'handwritten/' + MODULE + '.lean', 'project/ShielddSecurity/' + MODULE + '.lean']:
    assert pin(stopped / name) in plan['pins']
    add(stopped / name, 'preparation-stopped-01/' + name, 'mapping selector preparation error before plan/Lean admission; zero proof/control credit')
partial_pool = DIAG / 'transfer-pending-set-invariant-owned-floor-20261011-01/composition-review.json'
assert pin(partial_pool) in plan['pins']
add(partial_pool, 'preparation-stopped-01/owned-composition-review.json', 'original partial preparation metadata only; no object bytes or replay credit')
review['stopped_preparations'] = 1
review['stopped_preparation_scope'] = 'NameError from selector matching prior_mapping assignment; no plan admitted, no Lean job/events/object. Maintained preparation selector anchored to standalone mapping; exact source unchanged in fresh successor.'
dump(ROOT / 'review.json', review)
"""
s=s.replace(needle,history+needle)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':395,'owned_modules':40,'stopped_preparation':1})
