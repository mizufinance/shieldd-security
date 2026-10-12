from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-canonical-source-membership-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-canonical-source-membership-20261011-02'","CURRENT = DIAG / 'transfer-word-stage-order-20261011-02'"),
 ("MODULE = 'TransferCanonicalSourceMembership01'","MODULE = 'TransferWordStageOrder01'"),
 ("CHECKPOINT = DIAG / 'transfer-canonical-source-membership-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-word-stage-order-checkpoint-20261011-02'"),
 ("manager_endpoint = DIAG / 'transfer-canonical-source-publication-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-canonical-source-membership-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-canonical-source-publication-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-canonical-source-membership-endpoint01.tar.xz'"),
 ('02d0e580fc0168ac1540073a08a2765746ffa758d2aeae940d3e8f8bec562165','7d395ddd508cc7eac8a7c9257c072fe23311ace3fa3d83ece900e04acf544046'),
 ("tar.extractfile('reports/fresh-5-complete-declarations.txt')","tar.extractfile('reports/fresh-6-complete-declarations.txt')"),
 ('assert len(manager_reports) == 5','assert len(manager_reports) == 6'),
 ("'module': 'TransferCanonicalSourcePublication01'","'module': 'TransferCanonicalSourceMembership01'"),
 ("reference = {'canonical_source_publication':","reference = {'canonical_source_membership':"),
 ("'imported_complete_reports': 5","'imported_complete_reports': 6")]:replace(a,b)
s=s.replace('129','130').replace('1087','1093')
replace('assert len(fresh) == 6','assert len(fresh) == 8')
replace("assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 5","assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 5")
replace("add(stdout, 'reports/fresh-6-complete-declarations.txt'","add(stdout, 'reports/fresh-8-complete-declarations.txt'")
replace("'fresh_complete_public_audits': 6","'fresh_complete_public_audits': 8")
replace("'fresh_audits': 6, 'inherited_audits': 1093","'fresh_audits': 8, 'inherited_audits': 1093",2)
s=s.replace('transfer-canonical-source-membership-endpoint-v1','transfer-word-stage-order-endpoint-v1').replace('one-hundred-twenty-nine-module','one-hundred-thirty-module').replace('CANONICAL_SOURCE_ORD_MEMBERSHIP_AND_ORIGINAL_FIELD_UNIQUENESS_QUALIFIED','CANONICAL_WORD_SOURCE_STAGING_CHECK_ORDER_AND_GUARDED_ORIGINAL_APPEND_QUALIFIED')
replace("archive = ROOT / 'portable-windows-canonical-source-membership-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-stage-order-endpoint01.tar.xz'")
start=s.index("pressure=DIAG/'transfer-canonical-source-membership-20261011-01'");end=s.index("row=mapping['sct_pending_read_source_shape']",start)
s=s[:start]+s[start:end].replace('transfer-canonical-source-membership-20261011-01','transfer-word-stage-order-20261011-01').replace('TransferCanonicalSourceMembership01','TransferWordStageOrder01').replace('rejected-membership-attempt01','rejected-stage-attempt01')+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained, three definitions/five theorems. Source stage checks local duplicates before typed access, then distinct wrong-type panic and sealed returned refusal, then capacity/freshness/optional reader admission before guarded same-type original field append. Durable reader/native callback/collection/compiler bindings remain OPEN. First physical pressure attempt retained with zero credit; prior metadata repair histories preserved in ancestry. No native/control/certification or accepted ancestor replay credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-word-stage-order-checkpoint-20261011-02';checkpoint.mkdir(exist_ok=False)
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-canonical-source-membership-checkpoint-20261011-02/preservation_check.py').read_bytes())
print({'fresh_reports':8,'inherited_reports':1093,'owned_modules':130,'pressure_history':True})
