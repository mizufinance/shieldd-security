from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-stage-invariant-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-stage-invariant-20261011-01'","CURRENT = DIAG / 'transfer-checked-word-walk-20261011-01'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-stage-invariant-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-checked-word-walk-checkpoint-20261011-01'"),
 ("MODULE = 'TransferCheckedWordStageInvariant01'","MODULE = 'TransferCheckedWordWalk01'"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-nullify-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-checked-word-stage-invariant-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-nullify-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-stage-invariant-endpoint01.tar.xz'"),
 ('d8dfed6a73cfe4510a1c4edbccf42b58e261da948a0f53f9e889535c8cc57f98','24cb276ad8514c967259f16ea29b9ac23c297737670a36e6001e7e212f83c70e'),
 ("'module': 'TransferCheckedWordNullify01'","'module': 'TransferCheckedWordStageInvariant01'"),
 ("reference = {'checked_word_nullify':","reference = {'checked_word_stage_invariant':"),
 ('assert len(manager_reports) == 6','assert len(manager_reports) == 2'),
 ("manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-2-complete-declarations.txt')"),
 ('assert len(fresh) == 2','assert len(fresh) == 4'),
 ("assert declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 2","assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 3"),
 ("add(stdout, 'reports/fresh-2-complete-declarations.txt'","add(stdout, 'reports/fresh-4-complete-declarations.txt'"),
 ("'fresh_complete_public_audits': 2","'fresh_complete_public_audits': 4")]:replace(a,b)
s=s.replace('== 138','== 139').replace('== 1142','== 1144').replace("'inherited_complete_public_audits': 1142","'inherited_complete_public_audits': 1144")
replace("'fresh_audits': 2, 'inherited_audits': 1142","'fresh_audits': 4, 'inherited_audits': 1144",2)
s=s.replace('transfer-checked-word-stage-invariant-endpoint-v1','transfer-checked-word-walk-endpoint-v1').replace('one-hundred-thirty-eight-module','one-hundred-thirty-nine-module').replace('1142 original inherited complete reports','1144 original inherited complete reports').replace('verified 1142 inherited reports','verified 1144 inherited reports').replace('CHECKED_WORD_STAGE_DERIVES_INSPECTION_AND_PROPAGATES_SYMBOLIC_INVARIANT_QUALIFIED','WHOLE_PUBLIC_CHECKED_WORD_WALK_DERIVES_GLOBAL_ORDER_INVARIANT_AND_OBSERVATIONS_QUALIFIED')
replace("archive = ROOT / 'portable-windows-checked-word-stage-invariant-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-walk-endpoint01.tar.xz'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Four complete audits, one definition/three theorems. Symbolic induction derives every actual selected-cache stage and remaining walk from returned execution, propagates coherence/Nodup/capacity, exact ordered global source keys and all durable false lookups/other-key frames. Empty batch and missing-source checks retained. Only prior inductive invariant supplied, no expected output/typed getter/reader/codec premise. First attempt passes; no ancestors replayed. Native/full Transfer OPEN.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-checked-word-walk-checkpoint-20261011-01';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-checked-word-stage-invariant-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':4,'inherited_reports':1144,'owned_modules':139,'counts_derived_from_originals':True})
