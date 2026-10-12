from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-stage-refinement-endpoint-20261011-04/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-stage-refinement-20261011-04'","CURRENT = DIAG / 'transfer-word-stage-cache-publication-20261011-03'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-stage-refinement-checkpoint-20261011-04'","CHECKPOINT = DIAG / 'transfer-word-stage-cache-publication-checkpoint-20261011-03'"),
 ("MODULE = 'TransferCheckedWordStageRefinement01'","MODULE = 'TransferWordStageCachePublication01'"),
 ("manager_endpoint = DIAG / 'transfer-word-stage-numeric-refinement-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-checked-word-stage-refinement-endpoint-20261011-04'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-stage-numeric-refinement-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-stage-refinement-endpoint01.tar.xz'"),
 ('9bd6301940c7652faa22d8defa56a16784f6264906e748b23f91a2ef6ab1a39a','df1a857d469391f95b0a04a16ec1070803404214a93cc8d880bbce2d974bd856'),
 ("'module': 'TransferWordStageNumericRefinement01'","'module': 'TransferCheckedWordStageRefinement01'"),
 ("reference = {'word_stage_numeric_refinement':","reference = {'checked_word_stage_refinement':"),
 ('assert len(manager_reports) == 6','assert len(manager_reports) == 8'),
 ("manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-8-complete-declarations.txt')"),
 ('assert len(fresh) == 8','assert len(fresh) == 4'),
 ("assert declaration_kinds.count('def') == 4 and declaration_kinds.count('theorem') == 4","assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 3"),
 ("add(stdout, 'reports/fresh-8-complete-declarations.txt'","add(stdout, 'reports/fresh-4-complete-declarations.txt'"),
 ("'fresh_complete_public_audits': 8","'fresh_complete_public_audits': 4"),
 ("'rejected_attempts': 3","'rejected_attempts': 2")]:replace(a,b)
s=s.replace('== 133','== 134').replace('== 1113','== 1121').replace("'inherited_complete_public_audits': 1113","'inherited_complete_public_audits': 1121")
replace("'fresh_audits': 8, 'inherited_audits': 1113","'fresh_audits': 4, 'inherited_audits': 1121",2)
s=s.replace('transfer-checked-word-stage-refinement-endpoint-v1','transfer-word-stage-cache-publication-endpoint-v1').replace('one-hundred-thirty-three-module','one-hundred-thirty-four-module').replace('ALL_CHECKED_WORD_STAGE_BRANCHES_REFINE_CHECKED_NUMERIC_OUTCOMES_QUALIFIED','RETURNED_CHECKED_WORD_STAGE_DERIVES_ACTUAL_CACHE_PUBLICATION_AND_GETTER_QUALIFIED')
replace("archive = ROOT / 'portable-windows-checked-word-stage-refinement-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-stage-cache-publication-endpoint01.tar.xz'")
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['sct_pending_read_source_shape']",start)
s=s[:start]+"for attempt in [1,2]:\n    failed=DIAG/('transfer-word-stage-cache-publication-20261011-0'+str(attempt))\n    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageCachePublication01.lean','project/ShielddSecurity/TransferWordStageCachePublication01.lean','runs/01-TransferWordStageCachePublication01/stdout.txt']\n    for name in names:\n        row=pin(failed/name)\n        assert row in plan['pins']\n        add(failed/name,'rejected-cache-stage-attempt0'+str(attempt)+'/'+name,'exact original proof failure or physical pressure stop; entire attempt zero credit')\n"+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Four complete audits, one definition/three theorems, retained. Actual returned cache operation derives written original fields, checked getter, frames and checked numeric success. First proof elimination/unfolding failure and second zero-byte pressure stop retained as20 raw files with zero credit. Fresh proof search/rewritten witness repairs only; definitions/contracts/guards unchanged. Native bindings/full Transfer OPEN.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-word-stage-cache-publication-checkpoint-20261011-03';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-checked-word-stage-refinement-checkpoint-20261011-04/preservation_check.py').read_bytes())
print({'fresh_reports':4,'inherited_reports':1121,'owned_modules':134,'rejected_attempts':2})
