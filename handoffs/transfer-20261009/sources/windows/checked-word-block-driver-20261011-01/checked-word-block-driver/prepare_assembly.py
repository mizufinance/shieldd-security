from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-walk-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-walk-20261011-01'","CURRENT = DIAG / 'transfer-checked-word-block-driver-20261011-03'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-walk-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-checked-word-block-driver-checkpoint-20261011-03'"),
 ("MODULE = 'TransferCheckedWordWalk01'","MODULE = 'TransferCheckedWordBlockDriver01'"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-stage-invariant-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-checked-word-walk-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-stage-invariant-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-walk-endpoint01.tar.xz'"),
 ('24cb276ad8514c967259f16ea29b9ac23c297737670a36e6001e7e212f83c70e','ad0af22d5d27bf6583dea92e4393c53c8f51fba27f8f7f511e0f2d6674da6669'),
 ("'module': 'TransferCheckedWordStageInvariant01'","'module': 'TransferCheckedWordWalk01'"),
 ("reference = {'checked_word_stage_invariant':","reference = {'checked_word_walk':"),
 ('assert len(manager_reports) == 2','assert len(manager_reports) == 4'),
 ("manager_stdout = tar.extractfile('reports/fresh-2-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')"),
 ('assert len(fresh) == 4','assert len(fresh) == 5'),
 ("assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 3"),
 ("add(stdout, 'reports/fresh-4-complete-declarations.txt'","add(stdout, 'reports/fresh-5-complete-declarations.txt'"),
 ("'fresh_complete_public_audits': 4","'fresh_complete_public_audits': 5"),
 ("'rejected_attempts': 0","'rejected_attempts': 2")]:replace(a,b)
s=s.replace('== 139','== 140').replace('== 1144','== 1148').replace("'inherited_complete_public_audits': 1144","'inherited_complete_public_audits': 1148")
replace("'fresh_audits': 4, 'inherited_audits': 1144","'fresh_audits': 5, 'inherited_audits': 1148",2)
s=s.replace('transfer-checked-word-walk-endpoint-v1','transfer-checked-word-block-driver-endpoint-v1').replace('one-hundred-thirty-nine-module','one-hundred-forty-module').replace('1144 original inherited complete reports','1148 original inherited complete reports').replace('verified 1144 inherited reports','verified 1148 inherited reports').replace('WHOLE_PUBLIC_CHECKED_WORD_WALK_DERIVES_GLOBAL_ORDER_INVARIANT_AND_OBSERVATIONS_QUALIFIED','CONSTRUCTED_WHOLE_CHECKED_WORD_BLOCK_DERIVES_ACTUAL_ORIGINAL_GLOBAL_FIELD_GETTER_QUALIFIED')
replace("archive = ROOT / 'portable-windows-checked-word-walk-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-block-driver-endpoint01.tar.xz'")
at=s.index("row=mapping['checked_word_seal_source_shape']")
s=s[:at]+"for attempt in [1,2]:\n    failed=DIAG/('transfer-checked-word-block-driver-20261011-0'+str(attempt))\n    for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordBlockDriver01.lean','project/ShielddSecurity/TransferCheckedWordBlockDriver01.lean','runs/01-TransferCheckedWordBlockDriver01/stdout.txt']:\n        row=pin(failed/name)\n        assert row in plan['pins']\n        add(failed/name,'rejected-checked-block-attempt0'+str(attempt)+'/'+name,'exact original result-bind normalization or seal-witness proof error, full placeholder reports preserved; entire attempt zero credit')\n"+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Five complete audits, two definitions/three theorems. Constructed whole checked-word public walk then source seal derives actual getter of every original canonical source field, key uniqueness/capacity, every durable false lookup and other-key frames. Only observed initial absence and returned whole run supplied; intermediate walk/seal and inductive invariants derived. No desired state/getter/codec/domain premise. Two original proof errors retained20 raw artifacts, zero credit; bind normalization/witness repairs only, definitions/contracts/guards unchanged. Native/full Transfer OPEN.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-checked-word-block-driver-checkpoint-20261011-03';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-checked-word-walk-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':5,'inherited_reports':1148,'owned_modules':140,'counts_derived_from_originals':True})
