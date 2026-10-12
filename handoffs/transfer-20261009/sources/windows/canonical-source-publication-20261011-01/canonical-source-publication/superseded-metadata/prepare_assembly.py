from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-canonical-source-word-retention-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-canonical-source-word-retention-20261011-01'","CURRENT = DIAG / 'transfer-canonical-source-publication-20261011-01'"),
 ("MODULE = 'TransferCanonicalSourceWordRetention01'","MODULE = 'TransferCanonicalSourcePublication01'"),
 ("CHECKPOINT = DIAG / 'transfer-canonical-source-word-retention-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-canonical-source-publication-checkpoint-20261011-01'"),
 ("manager_endpoint = DIAG / 'transfer-word-sct-pending-read-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-canonical-source-word-retention-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-sct-pending-read-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-canonical-source-word-retention-endpoint01.tar.xz'"),
 ('bb471e9370abf85edc84032ad04cfd3e2a6657410ccf00c7b7901a08e07de516','a73c5de332a59b0aa773caeb664400521dad3094b7b6599f31ecca29a20c6e0d'),
 ("tar.extractfile('reports/fresh-8-complete-declarations.txt')","tar.extractfile('reports/fresh-3-complete-declarations.txt')"),
 ('assert len(manager_reports) == 8','assert len(manager_reports) == 3'),
 ("'module': 'TransferWordSctPendingRead01'","'module': 'TransferCanonicalSourceWordRetention01'"),
 ("reference = {'word_sct_pending_read':","reference = {'canonical_source_word_retention':"),
 ("'imported_complete_reports': 8","'imported_complete_reports': 3")]:replace(a,b)
s=s.replace('127','128').replace('1079','1082')
replace('assert len(fresh) == 3','assert len(fresh) == 5')
replace("add(stdout, 'reports/fresh-3-complete-declarations.txt'","add(stdout, 'reports/fresh-5-complete-declarations.txt'")
replace("'fresh_complete_public_audits': 3","'fresh_complete_public_audits': 5")
replace("'fresh_audits': 3, 'inherited_audits': 1082","'fresh_audits': 5, 'inherited_audits': 1082",2)
s=s.replace('transfer-canonical-source-word-retention-endpoint-v1','transfer-canonical-source-publication-endpoint-v1').replace('one-hundred-twenty-seven-module','one-hundred-twenty-eight-module').replace('CANONICAL_SOURCE_RAW_WORD_AND_ORDERED_FIELD_RETENTION_QUALIFIED','CANONICAL_SOURCE_WHOLE_BLOCK_ORIGINAL_FIELDS_AND_CHECKED_SCT_PUBLICATION_QUALIFIED')
replace("archive = ROOT / 'portable-windows-canonical-source-word-retention-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-canonical-source-publication-endpoint01.tar.xz'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Five first-pass full type/axiom audits retained, two definitions/three theorems. Whole returned canonical typed source execution derives exact original ordered fields in reached sealed object and checked SCT getter, exact accepted source keys and application root/Ready/Idle/physical roots/boundary. No caller final-state/walk/domain/inverse/getter/frame premise. Native binding OPEN; no native/control/certification or ancestor replay credit; all original histories retained.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-canonical-source-publication-checkpoint-20261011-01';checkpoint.mkdir(exist_ok=False)
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-canonical-source-word-retention-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':5,'inherited_reports':1082,'owned_modules':128,'first_pass':True})
