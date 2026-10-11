"""Seal ordered participant source proof with failed original retained at zero credit."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-writer-commit-source-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-writer-commit-source-20261011-01'", "CURRENT = DIAG / 'transfer-store-commit-source-20261011-02'")
s=s.replace('transfer-writer-commit-source-checkpoint-20261011-01','transfer-store-commit-source-checkpoint-20261011-02')
s=s.replace('writer-commit-source-endpoint','store-commit-source-endpoint')
replace("MODULE = 'TransferWriterCommitSource01'", "MODULE = 'TransferStoreCommitSource01'")
replace('assert len(fresh) == 9','assert len(fresh) == 13')
replace("assert pool['objects'] == 49 and len(pool['inherited_public_reports']) == 486", "assert pool['objects'] == 51 and len(pool['inherited_public_reports']) == 505")
replace("manager_endpoint = DIAG / 'transfer-writer-seal-discard-source-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-persist-intent-source-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-writer-seal-discard-source-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-persist-intent-source-endpoint01.tar.xz'")
replace('eb36c3b1ec22e0bc8a63d0496795cd38098835713072e248fbaf13d33e45e7ad','83ab4adf19f57bb007d3609395f89544d960a7f8da10819d0c9a7d7a8b3518e7')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-10-complete-declarations.txt')")
replace('assert len(manager_reports) == 13','assert len(manager_reports) == 10')
replace("'module': 'TransferWriterSealDiscardSource01'", "'module': 'TransferPersistIntentSource01'")
replace('assert len(combined_reports) == 486','assert len(combined_reports) == 505')
replace('assert len(manager_selected) == 49','assert len(manager_selected) == 51')
replace("reference = {'writer_seal_discard_source':", "reference = {'persist_intent_source':")
replace("'imported_complete_reports': 13", "'imported_complete_reports': 10")
replace("'complete_owned_modules': 49, 'inherited_complete_reports': 486", "'complete_owned_modules': 51, 'inherited_complete_reports': 505")
s=s.replace('Exact forty-nine-module whole/current pending/durable reader/source capacity/global block/one-shot seal/source prepare/finite codec/reachable block/writer preparation/seal-discard/status/commit closure, with 486 original inherited complete reports', 'Exact fifty-one-module whole/current pending/durable reader/source capacity/global block/seal/source prepare/finite codec/writer/intent/ordered participants closure, with 505 original inherited complete reports')
replace("add(stdout, 'reports/fresh-9-complete-declarations.txt'", "add(stdout, 'reports/fresh-13-complete-declarations.txt'")
s=s.replace('source writer commit program definitions and six ordered call/phase/owner refusal/post-Ready capacity/same-frozen input proofs','source ordered session recurrence/program definitions and six derived participant/readiness/observed-root/intent gate proofs')
s=s.replace('complete forty-nine-module first import root','complete fifty-one-module first import root')
s=s.replace('verified 486 inherited reports','verified 505 inherited reports')
s=s.replace('SOURCE_WRITER_COMMIT_ORDER_INTERRUPTION_AND_POST_READY_CAPACITY_ERROR_QUALIFIED','SOURCE_STORE_COMMIT_ORDERED_PARTICIPANTS_OBSERVED_ROOTS_AND_BLOCKED_READINESS_QUALIFIED')
replace("'fresh_definition_audits': 3", "'fresh_definition_audits': 7")
replace("'fresh_complete_public_audits': 9", "'fresh_complete_public_audits': 13")
replace("'inherited_complete_public_audits': 486", "'inherited_complete_public_audits': 505")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All thirteen declarations have original complete type/axiom reports. Ordered session success is derived symbolically from recurrence outcome; observed failed roots remain retained and no suffix is invoked. Final root match and intent equality are derived from whole returned transition success, with ready still blocked. Native session/root/lock/I/O/type/ownership/durability remain interfaces; zero native/control/full certification credit.'}"+s[end:]
s=s.replace("'fresh_audits': 9, 'inherited_audits': 486", "'fresh_audits': 13, 'inherited_audits': 505")
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"; assert s.count(anchor)==1
extra="""add(CURRENT / 'repair_recipe.py', 'qualified/repair_recipe.py', 'impossible Option cases and reflexive rewritten receipts; program/contracts unchanged')
failed = DIAG / 'transfer-store-commit-source-20261011-01'
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferStoreCommitSource01.lean', 'project/ShielddSecurity/TransferStoreCommitSource01.lean', 'runs/01-TransferStoreCommitSource01/stdout.txt']:
    add(failed / name, 'rejected/attempt01/' + name, 'full failed original attempt; zero proof/native/control credit')
"""
s=s.replace(anchor,extra+anchor).replace("'rejected_attempts': 0", "'rejected_attempts': 1")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':13,'inherited_reports':505,'owned_modules':51,'rejected_proof_credit':0})
