from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-sct-pending-read-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-sct-pending-read-20261011-01'","CURRENT = DIAG / 'transfer-canonical-source-word-retention-20261011-01'"),
 ("MODULE = 'TransferWordSctPendingRead01'","MODULE = 'TransferCanonicalSourceWordRetention01'"),
 ("CHECKPOINT = DIAG / 'transfer-word-sct-pending-read-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-canonical-source-word-retention-checkpoint-20261011-01'"),
 ("manager_endpoint = DIAG / 'transfer-word-object-put-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-word-sct-pending-read-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-object-put-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-sct-pending-read-endpoint01.tar.xz'"),
 ('7259fe8a640eb7ead7a68a71553a3ac354db9e5e143fca377a477b39036842f1','bb471e9370abf85edc84032ad04cfd3e2a6657410ccf00c7b7901a08e07de516'),
 ("'module': 'TransferWordObjectPut01'","'module': 'TransferWordSctPendingRead01'"),
 ("reference = {'word_object_put':","reference = {'word_sct_pending_read':")]:replace(a,b)
s=s.replace('126','127').replace('1071','1079')
replace('assert len(fresh) == 8','assert len(fresh) == 3')
replace("add(stdout, 'reports/fresh-8-complete-declarations.txt'","add(stdout, 'reports/fresh-3-complete-declarations.txt'")
replace("'fresh_complete_public_audits': 8","'fresh_complete_public_audits': 3")
replace("'fresh_audits': 8, 'inherited_audits': 1079","'fresh_audits': 3, 'inherited_audits': 1079",2)
s=s.replace('transfer-word-sct-pending-read-endpoint-v1','transfer-canonical-source-word-retention-endpoint-v1').replace('one-hundred-twenty-six-module','one-hundred-twenty-seven-module').replace('SOURCE_SCT_PENDING_GETTER_ABSENCE_OPEN_SEALED_AND_PANIC_BRANCHES_QUALIFIED','CANONICAL_SOURCE_RAW_WORD_AND_ORDERED_FIELD_RETENTION_QUALIFIED')
replace("archive = ROOT / 'portable-windows-word-sct-pending-read-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-canonical-source-word-retention-endpoint01.tar.xz'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Three first-pass complete theorem audits retained. Canonical source typed input projects to source key then word-field encoder recovers exact original raw vector, entire canonical typed scalar, and ordered list without caller inverse or desired fields. Native canonical Scalar invariant and implementation correspondence remain OPEN. All ancestor histories retained, zero replay/native/control/certification credit; full Transfer OPEN.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-canonical-source-word-retention-checkpoint-20261011-01';checkpoint.mkdir(exist_ok=False)
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-word-sct-pending-read-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':3,'inherited_reports':1079,'owned_modules':127,'first_pass':True})
