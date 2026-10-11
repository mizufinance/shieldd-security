"""Seal observed intent persistence; retain rejected proof attempt without credit."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-writer-commit-source-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-writer-commit-source-20261011-01'", "CURRENT = DIAG / 'transfer-persist-intent-source-20261011-02'")
s=s.replace('transfer-writer-commit-source-checkpoint-20261011-01','transfer-persist-intent-source-checkpoint-20261011-02')
s=s.replace('writer-commit-source-endpoint','persist-intent-source-endpoint')
replace("MODULE = 'TransferWriterCommitSource01'", "MODULE = 'TransferPersistIntentSource01'")
replace('assert len(fresh) == 9','assert len(fresh) == 10')
replace("assert pool['objects'] == 49 and len(pool['inherited_public_reports']) == 486", "assert pool['objects'] == 50 and len(pool['inherited_public_reports']) == 495")
replace("manager_endpoint = DIAG / 'transfer-writer-seal-discard-source-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-writer-commit-source-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-writer-seal-discard-source-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-writer-commit-source-endpoint01.tar.xz'")
replace('eb36c3b1ec22e0bc8a63d0496795cd38098835713072e248fbaf13d33e45e7ad','44d75fa9ff6f88406c3fac3d6d6e2f6ae55c58c9005f3baef586cd0f17e58a9b')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-9-complete-declarations.txt')")
replace('assert len(manager_reports) == 13','assert len(manager_reports) == 9')
replace("'module': 'TransferWriterSealDiscardSource01'", "'module': 'TransferWriterCommitSource01'")
replace('assert len(combined_reports) == 486','assert len(combined_reports) == 495')
replace('assert len(manager_selected) == 49','assert len(manager_selected) == 50')
replace("reference = {'writer_seal_discard_source':", "reference = {'writer_commit_source':")
replace("'imported_complete_reports': 13", "'imported_complete_reports': 9")
replace("'complete_owned_modules': 49, 'inherited_complete_reports': 486", "'complete_owned_modules': 50, 'inherited_complete_reports': 495")
s=s.replace('Exact forty-nine-module whole/current pending/durable reader/source capacity/global block/one-shot seal/source prepare/finite codec/reachable block/writer preparation/seal-discard/status/commit closure, with 486 original inherited complete reports', 'Exact fifty-module whole/current pending/durable reader/source capacity/global block/one-shot seal/source prepare/finite codec/reachable block/writer preparation/seal-discard/status/commit/intent closure, with 495 original inherited complete reports')
replace("add(stdout, 'reports/fresh-9-complete-declarations.txt'", "add(stdout, 'reports/fresh-10-complete-declarations.txt'")
s=s.replace('source writer commit program definitions and six ordered call/phase/owner refusal/post-Ready capacity/same-frozen input proofs','source intent filesystem/program definitions and four idempotence/observed-progress/failure-readiness proofs')
s=s.replace('complete forty-nine-module first import root','complete fifty-module first import root')
s=s.replace('verified 486 inherited reports','verified 495 inherited reports')
s=s.replace('SOURCE_WRITER_COMMIT_ORDER_INTERRUPTION_AND_POST_READY_CAPACITY_ERROR_QUALIFIED','SOURCE_PERSIST_INTENT_OBSERVED_PROGRESS_READINESS_AND_IDEMPOTENCE_QUALIFIED')
replace("'fresh_definition_audits': 3", "'fresh_definition_audits': 6")
replace("'fresh_theorem_audits': 6", "'fresh_theorem_audits': 4")
replace("'fresh_complete_public_audits': 9", "'fresh_complete_public_audits': 10")
replace("'inherited_complete_public_audits': 486", "'inherited_complete_public_audits': 495")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All ten declarations have original complete type/axiom reports. Actual existing equal intent is idempotent; failed new write retains independently observed filesystem progress, blocks ready and derives original Readback status unavailability. Native I/O/durable file/directory/lock/type/owner/Clone correspondences remain explicit. Error does not infer absence or rollback; zero native/control/full certification credit.'}"+s[end:]
s=s.replace("'fresh_audits': 9, 'inherited_audits': 486", "'fresh_audits': 10, 'inherited_audits': 495")
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"; assert s.count(anchor)==1
extra="""add(CURRENT / 'repair_recipe.py', 'qualified/repair_recipe.py', 'rewrite failed write before Store unfolding; program and contracts unchanged')
failed = DIAG / 'transfer-persist-intent-source-20261011-01'
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferPersistIntentSource01.lean', 'project/ShielddSecurity/TransferPersistIntentSource01.lean', 'runs/01-TransferPersistIntentSource01/stdout.txt']:
    add(failed / name, 'rejected/attempt01/' + name, 'full failed original attempt; zero proof/native/control credit')
"""
s=s.replace(anchor,extra+anchor).replace("'rejected_attempts': 0", "'rejected_attempts': 1")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':10,'inherited_reports':495,'owned_modules':50,'rejected_proof_credit':0})
