from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-stage-cache-publication-endpoint-20261011-04/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-stage-cache-publication-20261011-03'","CURRENT = DIAG / 'transfer-checked-word-seal-20261011-03'"),
 ("CHECKPOINT = DIAG / 'transfer-word-stage-cache-publication-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-checked-word-seal-checkpoint-20261011-03'"),
 ("MODULE = 'TransferWordStageCachePublication01'","MODULE = 'TransferCheckedWordSeal01'"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-stage-refinement-endpoint-20261011-04'","manager_endpoint = DIAG / 'transfer-word-stage-cache-publication-endpoint-20261011-04'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-stage-refinement-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-stage-cache-publication-endpoint01.tar.xz'"),
 ('df1a857d469391f95b0a04a16ec1070803404214a93cc8d880bbce2d974bd856','173c3f3a7e5c03ce7f0a67f1fbd83f0fc7ea2e17b05bdad9a90af41bfea8a805'),
 ("'module': 'TransferCheckedWordStageRefinement01'","'module': 'TransferWordStageCachePublication01'"),
 ("reference = {'checked_word_stage_refinement':","reference = {'word_stage_cache_publication':"),
 ('assert len(manager_reports) == 8','assert len(manager_reports) == 4'),
 ("manager_stdout = tar.extractfile('reports/fresh-8-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')"),
 ('assert len(fresh) == 4','assert len(fresh) == 8'),
 ("assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 6"),
 ("add(stdout, 'reports/fresh-4-complete-declarations.txt'","add(stdout, 'reports/fresh-8-complete-declarations.txt'"),
 ("'fresh_complete_public_audits': 4","'fresh_complete_public_audits': 8")]:replace(a,b)
s=s.replace('== 134','== 135').replace('== 1121','== 1125').replace("'inherited_complete_public_audits': 1121","'inherited_complete_public_audits': 1125")
replace("'fresh_audits': 4, 'inherited_audits': 1121","'fresh_audits': 8, 'inherited_audits': 1125",2)
s=s.replace('transfer-word-stage-cache-publication-endpoint-v1','transfer-checked-word-seal-endpoint-v1').replace('one-hundred-thirty-four-module','one-hundred-thirty-five-module').replace('1121 original inherited complete reports','1125 original inherited complete reports').replace('verified 1121 inherited reports','verified 1125 inherited reports').replace('RETURNED_CHECKED_WORD_STAGE_DERIVES_ACTUAL_CACHE_PUBLICATION_AND_GETTER_QUALIFIED','CHECKED_WORD_SEAL_PRESERVES_ORIGINAL_ORDERED_FIELDS_AND_BRANCHES_QUALIFIED')
replace("archive = ROOT / 'portable-windows-word-stage-cache-publication-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-seal-endpoint01.tar.xz'")
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['sct_pending_read_source_shape']",start)
s=s[:start]+"for attempt in [1,2]:\n    failed=DIAG/('transfer-checked-word-seal-20261011-0'+str(attempt))\n    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/checked-word-seal-shape.json','handwritten/TransferCheckedWordSeal01.lean','project/ShielddSecurity/TransferCheckedWordSeal01.lean','runs/01-TransferCheckedWordSeal01/stdout.txt']\n    if attempt==2:names.append('rejected-object-identity.json')\n    for name in names:\n        row=pin(failed/name)\n        assert row in plan['pins']\n        add(failed/name,'rejected-seal-attempt0'+str(attempt)+'/'+name,'exact original unused-binder warning or pressure stop; entire attempt zero credit')\nadd(CURRENT/'rejected-object-identity.json','context/rejected-seal-object-identity.json','original warning attempt object identity only, no object bytes or proof credit')\nrow=mapping['checked_word_seal_source_shape']\nassert pin(row['path'])==row and row in plan['pins']\nadd(row['path'],'context/checked-word-seal-shape.json','exact checked read/default/refusal/ordered-field put source shape, static association only')\n"+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
# Remove inherited endpoint correction-generation block; its authentic history remains in ancestry.
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete audits, two definitions/six theorems. Wrong-type panic and already-Sealed refusal retained; returned success derives actual prior absent/Open and exact original ordered fields. Returned stage constructs exact source seal. Original warning attempt compiled all reports but is wholly zero credit; object bytes excluded. Second pressure stop zero credit. Unused existential binder rename only; definitions/contracts/guards unchanged. Native/full Transfer OPEN.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-checked-word-seal-checkpoint-20261011-03';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-word-stage-cache-publication-checkpoint-20261011-03/preservation_check.py').read_bytes())
print({'fresh_reports':8,'inherited_reports':1125,'owned_modules':135,'counts_derived_from_originals':True})
