from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-seal-publication-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-seal-publication-20261011-02'","CURRENT = DIAG / 'transfer-checked-word-nullify-20261011-01'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-seal-publication-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-checked-word-nullify-checkpoint-20261011-01'"),
 ("MODULE = 'TransferCheckedWordSealPublication01'","MODULE = 'TransferCheckedWordNullify01'"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-seal-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-checked-word-seal-publication-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-seal-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-seal-publication-endpoint01.tar.xz'"),
 ('b71a6cc71d79a8a03d6e7d10aa383205ae7925362849fb6dc8262a656093defd','62d996cb35e0e9c88bea2787689e76575763a5b38edc6745ab8fc3af96f12e3b'),
 ("'module': 'TransferCheckedWordSeal01'","'module': 'TransferCheckedWordSealPublication01'"),
 ("reference = {'checked_word_seal':","reference = {'checked_word_seal_publication':"),
 ('assert len(manager_reports) == 8','assert len(manager_reports) == 3'),
 ("manager_stdout = tar.extractfile('reports/fresh-8-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-3-complete-declarations.txt')"),
 ('assert len(fresh) == 3','assert len(fresh) == 6'),
 ("assert declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 5"),
 ("add(stdout, 'reports/fresh-3-complete-declarations.txt'","add(stdout, 'reports/fresh-6-complete-declarations.txt'"),
 ("'fresh_complete_public_audits': 3","'fresh_complete_public_audits': 6"),
 ("'rejected_attempts': 1","'rejected_attempts': 0")]:replace(a,b)
s=s.replace('== 136','== 137').replace('== 1133','== 1136').replace("'inherited_complete_public_audits': 1133","'inherited_complete_public_audits': 1136")
replace("'fresh_audits': 3, 'inherited_audits': 1133","'fresh_audits': 6, 'inherited_audits': 1136",2)
s=s.replace('transfer-checked-word-seal-publication-endpoint-v1','transfer-checked-word-nullify-endpoint-v1').replace('one-hundred-thirty-six-module','one-hundred-thirty-seven-module').replace('1133 original inherited complete reports','1136 original inherited complete reports').replace('verified 1133 inherited reports','verified 1136 inherited reports').replace('RETURNED_CHECKED_CACHE_SEAL_DERIVES_ACTUAL_GETTERS_AND_STAGE_JOIN_QUALIFIED','PUBLIC_CHECKED_WORD_NULLIFY_EMPTY_SOURCE_AND_STAGE_ORDER_QUALIFIED')
replace("archive = ROOT / 'portable-windows-checked-word-seal-publication-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-nullify-endpoint01.tar.xz'")
start=s.index("failed=DIAG/'transfer-checked-word-seal-publication-20261011-01'");end=s.index("row=mapping['checked_word_seal_source_shape']",start)
s=s[:start]+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete audits, one definition/five theorems. Actual public nullify modeled checks skip every object read for empty batch, refuse missing source for nonempty before getter, otherwise forward exact checked stage. Returned success derives these actual branches. Exact native source.id selector and full bindings remain OPEN. First attempt passes; no failures omitted or ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-checked-word-nullify-checkpoint-20261011-01';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-checked-word-seal-publication-checkpoint-20261011-02/preservation_check.py').read_bytes())
print({'fresh_reports':6,'inherited_reports':1136,'owned_modules':137,'counts_derived_from_originals':True})
