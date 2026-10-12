from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-stage-order-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-stage-order-20261011-02'","CURRENT = DIAG / 'transfer-word-stage-admission-20261011-02'"),
 ("MODULE = 'TransferWordStageOrder01'","MODULE = 'TransferWordStageAdmission01'"),
 ("CHECKPOINT = DIAG / 'transfer-word-stage-order-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-word-stage-admission-checkpoint-20261011-02'"),
 ("manager_endpoint = DIAG / 'transfer-canonical-source-membership-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-word-stage-order-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-canonical-source-membership-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-stage-order-endpoint01.tar.xz'"),
 ('7d395ddd508cc7eac8a7c9257c072fe23311ace3fa3d83ece900e04acf544046','c0b4b515bec54e0b50dfeda26dfaaa94951d0a0b3e31626c8fdd6db4039856f7'),
 ("tar.extractfile('reports/fresh-6-complete-declarations.txt')","tar.extractfile('reports/fresh-8-complete-declarations.txt')"),
 ('assert len(manager_reports) == 6','assert len(manager_reports) == 8'),
 ("'module': 'TransferCanonicalSourceMembership01'","'module': 'TransferWordStageOrder01'"),
 ("reference = {'canonical_source_membership':","reference = {'word_stage_order':"),
 ("'imported_complete_reports': 6","'imported_complete_reports': 8")]:replace(a,b)
s=s.replace('130','131').replace('1093','1101')
replace('assert len(fresh) == 8','assert len(fresh) == 6')
replace("assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 5","assert declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 6")
replace("add(stdout, 'reports/fresh-8-complete-declarations.txt'","add(stdout, 'reports/fresh-6-complete-declarations.txt'")
replace("'fresh_complete_public_audits': 8","'fresh_complete_public_audits': 6")
replace("'fresh_audits': 8, 'inherited_audits': 1101","'fresh_audits': 6, 'inherited_audits': 1101",2)
s=s.replace('transfer-word-stage-order-endpoint-v1','transfer-word-stage-admission-endpoint-v1').replace('one-hundred-thirty-module','one-hundred-thirty-one-module').replace('CANONICAL_WORD_SOURCE_STAGING_CHECK_ORDER_AND_GUARDED_ORIGINAL_APPEND_QUALIFIED','RETURNED_CANONICAL_WORD_STAGE_DERIVES_ALL_ADMISSION_AND_ORIGINAL_FIELDS_QUALIFIED')
replace("archive = ROOT / 'portable-windows-word-stage-order-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-stage-admission-endpoint01.tar.xz'")
start=s.index("pressure=DIAG/'transfer-word-stage-order-20261011-01'");end=s.index("row=mapping['sct_pending_read_source_shape']",start)
block=s[start:end].replace('transfer-word-stage-order-20261011-01','transfer-word-stage-admission-20261011-01').replace('TransferWordStageOrder01','TransferWordStageAdmission01').replace('rejected-stage-attempt01','rejected-admission-attempt01').replace('original physical pressure stopped attempt, zero stdout/audits/objects, zero credit','original lint-warning rejected attempt; entire complete stdout and all reports zero credit')
block+="failed_object=pin(pressure/'project/ShielddSecurity/TransferWordStageAdmission01.olean')\nassert failed_object in plan['pins']\ndump(ROOT/'failed-object-identity.json',{'object':failed_object,'credit':0,'qualification':'original rejected lint attempt object retained and pinned locally; not imported or carried in portable archive'})\nadd(ROOT/'failed-object-identity.json','context/failed-object-identity.json','exact original uncredited object identity; no object bytes/replay/credit')\n"
s=s[:start]+block+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete theorem audits retained, no new definitions. Returned source-stage success derives actual prior typed Open/default branch, uniqueness, natural capacity, pending freshness, required reader success and exact original field append without admitted/desired-object premises. Original lint-warning attempt stdout/source/plan/events and locally retained uncredited object identity preserved, entire failed attempt zero credit; only local binder names repaired. Prior pressure and metadata histories preserved in ancestry. Native collection/reader/compiler/delta correspondence OPEN; no native/control/certification or accepted ancestor replay credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-word-stage-admission-checkpoint-20261011-02';checkpoint.mkdir(exist_ok=False)
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-word-stage-order-checkpoint-20261011-02/preservation_check.py').read_bytes())
print({'fresh_reports':6,'inherited_reports':1101,'owned_modules':131,'lint_history':True})
