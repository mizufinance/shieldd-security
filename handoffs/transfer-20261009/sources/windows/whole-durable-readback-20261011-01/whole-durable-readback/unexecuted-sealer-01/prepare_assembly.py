"""Seal full body/current durable readback join and exact two-branch ancestry."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-current-pending-replay-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-current-pending-replay-20261011-01'", "CURRENT = DIAG / 'transfer-whole-durable-readback-20261011-01'")
s=s.replace('transfer-current-pending-replay-checkpoint-20261011-01','transfer-whole-durable-readback-checkpoint-20261011-01')
s=s.replace('current-pending-replay-endpoint','whole-durable-readback-endpoint')
replace("MODULE = 'TransferCurrentPendingReplay01'", "MODULE = 'TransferWholeDurableReadback01'")
replace('assert len(fresh) == 8','assert len(fresh) == 11')
replace("assert pool['objects'] == 35 and len(pool['inherited_public_reports']) == 343", "assert pool['objects'] == 37 and len(pool['inherited_public_reports']) == 368")
replace("manager_endpoint = DIAG / 'transfer-nullifier-object-keys-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-current-pending-replay-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-nullifier-object-keys-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-current-pending-replay-endpoint01.tar.xz'")
replace('4596a11c227ab40856e24f331911de55ebb45b02719abd3b64b6eb195c873f79','23484b471486055e5bc1f0c2a754fa4b135ac415d272c6f1868606a3e2128b1d')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-8-complete-declarations.txt')")
replace('assert len(manager_reports) == 7','assert len(manager_reports) == 8')
replace("'module': 'TransferNullifierObjectKeys01'", "'module': 'TransferCurrentPendingReplay01'")
replace('assert len(combined_reports) == 343 and combined_reports == pool[\'inherited_public_reports\']',"""assert len(combined_reports) == 351
readback_endpoint = DIAG / 'transfer-readback-publication-endpoint-20261010-01'
readback_archive = readback_endpoint / 'portable-windows-readback-publication-endpoint01.tar.xz'
assert pin(readback_archive)['sha256'] == '48b33b403223914e40cfedfd0d6031e68bde14fa5b659a72823caed344de47a8'
assert pin(readback_archive) in plan['pins']
with tarfile.open(readback_archive, 'r:xz') as tar:
    readback_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    readback_events = [json.loads(line) for line in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    readback_stdout = tar.extractfile('reports/TransferReadback-complete-types-and-axioms.txt').read().decode()
    readback_reports = m.audit(readback_stdout, readback_plan['targets'][0]['audit_names'])
assert len(readback_reports) == 17 and readback_reports == readback_events[1]['result']['audits']
assert set(combined_reports).isdisjoint(readback_reports)
combined_reports.update(readback_reports)
manager_selected.append({'module': 'TransferReadback', 'source': readback_plan['targets'][0]['source'],
    'object': readback_events[1]['result']['objects'][0]})
assert len(combined_reports) == 368 and combined_reports == pool['inherited_public_reports']""")
replace('assert len(manager_selected) == 35','assert len(manager_selected) == 37')
replace('carriers = [pin(manager_archive)]','carriers = [pin(manager_archive), pin(readback_archive)]')
replace("reference = {'nullifier_object_keys':", "reference = {'current_pending_replay':")
replace("'imported_complete_reports': 7", "'imported_complete_reports': 8")
replace("'ancestors': manager_reference, 'complete_owned_modules': 35, 'inherited_complete_reports': 343", "'readback': {'archive': pin(readback_archive), 'manifest': pin(readback_endpoint / 'manifest.json'), 'imported_complete_reports': 17, 'scope': 'Exactly the original Readback source/object and seventeen full reports are reused; BankRecovery/WriterPublication modules are not imported by this join.'},\n    'ancestors': manager_reference, 'complete_owned_modules': 37, 'inherited_complete_reports': 368")
s=s.replace('Exact thirty-five-module closure through source-derived object keys, retained pending encoding and both complete-Item body/index/deferred branches, with all 343 inherited complete reports.', 'Exact thirty-seven-module closure joining whole body/current pending/source-key proofs to the original durable Readback model, with 368 inherited complete reports. Readback has no owned imports; shared StateDelta appears once.')
replace("add(stdout, 'reports/fresh-8-complete-declarations.txt'", "add(stdout, 'reports/fresh-11-complete-declarations.txt'")
s=s.replace('current typed object getter and whole two-action shared-input replay refusal','current typed Reader/boundary/lock/verified status and whole-delivery conditional authenticated absence')
s=s.replace('complete thirty-five-module first import root','complete thirty-seven-module first import root')
s=s.replace('verified 343 inherited reports','verified 368 inherited reports')
s=s.replace('CURRENT_TYPED_PENDING_READ_DERIVES_SHARED_INPUT_REPLAY_REFUSAL_QUALIFIED','WHOLE_TRANSFER_SUCCESS_DERIVES_VERIFIED_DURABLE_READBACK_AND_CONDITIONAL_AUTHENTICATED_ABSENCE_QUALIFIED')
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 8")
replace("'fresh_complete_public_audits': 8", "'fresh_complete_public_audits': 11")
replace("'inherited_complete_public_audits': 343", "'inherited_complete_public_audits': 368")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All three definitions and eight theorems have complete original type/axiom reports. Exactly seventeen old Readback reports are re-audited and source/object identities verified from the already accepted archive. No old Lean module or native control is replayed; no full Transfer certification credit.'}"+s[end:]
s=s.replace("'fresh_audits': 8, 'inherited_audits': 343", "'fresh_audits': 11, 'inherited_audits': 368")
replace("add(ROOT / 'prepare_assembly-rejected-selector.py', 'preparation-stopped/prepare_assembly-rejected-selector.py', 'unexecuted sealer preparation selector rejected before assembler creation; zero proof or control credit')\n",'')
needle="add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json'"
assert s.count(needle)==1
s=s.replace(needle,"add(DIAG / 'transfer-readback-recovery-publication-20261010-02/source-mapping.json', 'context/readback-source-association.json', 'exact old source association already pinned; semantic/native/codec/Merkle interfaces remain explicit')\n"+needle)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':11,'inherited_reports':368,'owned_modules':37})
