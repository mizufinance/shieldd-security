from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-nullify-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-nullify-20261011-01'","CURRENT = DIAG / 'transfer-checked-word-stage-invariant-20261011-01'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-nullify-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-checked-word-stage-invariant-checkpoint-20261011-01'"),
 ("MODULE = 'TransferCheckedWordNullify01'","MODULE = 'TransferCheckedWordStageInvariant01'"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-seal-publication-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-checked-word-nullify-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-seal-publication-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-nullify-endpoint01.tar.xz'"),
 ('62d996cb35e0e9c88bea2787689e76575763a5b38edc6745ab8fc3af96f12e3b','d8dfed6a73cfe4510a1c4edbccf42b58e261da948a0f53f9e889535c8cc57f98'),
 ("'module': 'TransferCheckedWordSealPublication01'","'module': 'TransferCheckedWordNullify01'"),
 ("reference = {'checked_word_seal_publication':","reference = {'checked_word_nullify':"),
 ('assert len(manager_reports) == 3','assert len(manager_reports) == 6'),
 ("manager_stdout = tar.extractfile('reports/fresh-3-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')"),
 ('assert len(fresh) == 6','assert len(fresh) == 2'),
 ("assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 5","assert declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 2"),
 ("add(stdout, 'reports/fresh-6-complete-declarations.txt'","add(stdout, 'reports/fresh-2-complete-declarations.txt'"),
 ("'fresh_complete_public_audits': 6","'fresh_complete_public_audits': 2")]:replace(a,b)
s=s.replace('== 137','== 138').replace('== 1136','== 1142').replace("'inherited_complete_public_audits': 1136","'inherited_complete_public_audits': 1142")
replace("'fresh_audits': 6, 'inherited_audits': 1136","'fresh_audits': 2, 'inherited_audits': 1142",2)
s=s.replace('transfer-checked-word-nullify-endpoint-v1','transfer-checked-word-stage-invariant-endpoint-v1').replace('one-hundred-thirty-seven-module','one-hundred-thirty-eight-module').replace('1136 original inherited complete reports','1142 original inherited complete reports').replace('verified 1136 inherited reports','verified 1142 inherited reports').replace('PUBLIC_CHECKED_WORD_NULLIFY_EMPTY_SOURCE_AND_STAGE_ORDER_QUALIFIED','CHECKED_WORD_STAGE_DERIVES_INSPECTION_AND_PROPAGATES_SYMBOLIC_INVARIANT_QUALIFIED')
replace("archive = ROOT / 'portable-windows-checked-word-nullify-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-stage-invariant-endpoint01.tar.xz'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Two complete theorem audits. Returned checked source stage derives actual numeric inspection with actual selected previous pending and durable reader; then prior inductive coherence/Nodup propagates to next invariant, exact ordered append, and every actual durable false lookup. No getter/domain/reader/admission/inverse/desired-result premise. First attempt passes; no ancestors replayed. Native/full Transfer OPEN.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-checked-word-stage-invariant-checkpoint-20261011-01';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-checked-word-nullify-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':2,'inherited_reports':1142,'owned_modules':138,'counts_derived_from_originals':True})
