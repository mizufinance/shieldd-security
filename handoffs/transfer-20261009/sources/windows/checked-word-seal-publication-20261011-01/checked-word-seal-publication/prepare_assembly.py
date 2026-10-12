from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-seal-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-seal-20261011-03'","CURRENT = DIAG / 'transfer-checked-word-seal-publication-20261011-02'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-seal-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-checked-word-seal-publication-checkpoint-20261011-02'"),
 ("MODULE = 'TransferCheckedWordSeal01'","MODULE = 'TransferCheckedWordSealPublication01'"),
 ("manager_endpoint = DIAG / 'transfer-word-stage-cache-publication-endpoint-20261011-04'","manager_endpoint = DIAG / 'transfer-checked-word-seal-endpoint-20261011-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-stage-cache-publication-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-seal-endpoint01.tar.xz'"),
 ('173c3f3a7e5c03ce7f0a67f1fbd83f0fc7ea2e17b05bdad9a90af41bfea8a805','b71a6cc71d79a8a03d6e7d10aa383205ae7925362849fb6dc8262a656093defd'),
 ("'module': 'TransferWordStageCachePublication01'","'module': 'TransferCheckedWordSeal01'"),
 ("reference = {'word_stage_cache_publication':","reference = {'checked_word_seal':"),
 ('assert len(manager_reports) == 4','assert len(manager_reports) == 8'),
 ("manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-8-complete-declarations.txt')"),
 ('assert len(fresh) == 8','assert len(fresh) == 3'),
 ("assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 6","assert declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 3"),
 ("add(stdout, 'reports/fresh-8-complete-declarations.txt'","add(stdout, 'reports/fresh-3-complete-declarations.txt'"),
 ("'fresh_complete_public_audits': 8","'fresh_complete_public_audits': 3"),
 ("'rejected_attempts': 2","'rejected_attempts': 1")]:replace(a,b)
s=s.replace('== 135','== 136').replace('== 1125','== 1133').replace("'inherited_complete_public_audits': 1125","'inherited_complete_public_audits': 1133")
replace("'fresh_audits': 8, 'inherited_audits': 1125","'fresh_audits': 3, 'inherited_audits': 1133",2)
s=s.replace('transfer-checked-word-seal-endpoint-v1','transfer-checked-word-seal-publication-endpoint-v1').replace('one-hundred-thirty-five-module','one-hundred-thirty-six-module').replace('1125 original inherited complete reports','1133 original inherited complete reports').replace('verified 1125 inherited reports','verified 1133 inherited reports').replace('CHECKED_WORD_SEAL_PRESERVES_ORIGINAL_ORDERED_FIELDS_AND_BRANCHES_QUALIFIED','RETURNED_CHECKED_CACHE_SEAL_DERIVES_ACTUAL_GETTERS_AND_STAGE_JOIN_QUALIFIED')
replace("archive = ROOT / 'portable-windows-checked-word-seal-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-seal-publication-endpoint01.tar.xz'")
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['checked_word_seal_source_shape']",start)
s=s[:start]+"failed=DIAG/'transfer-checked-word-seal-publication-20261011-01'\nassert not (failed/'runs/01-TransferCheckedWordSealPublication01/stdout.txt').exists()\nfor name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordSealPublication01.lean','project/ShielddSecurity/TransferCheckedWordSealPublication01.lean']:\n    row=pin(failed/name)\n    assert row in plan['pins']\n    add(failed/name,'rejected-seal-publication-pressure01/'+name,'exact original physical pressure stop before Lean; entire attempt zero credit')\n"+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Three complete theorem audits. Returned source cache seal derives actual selected sealed enum, actual ordered/isSealed/ensureSealed getters, and every other-key frame. Returned checked stage then checked seal derives original field append and consensus capacity. No expected cache, prior shape or getter-success premise. Original pressure stop9 raw files retained zero credit; same source and guards. Native/full Transfer OPEN.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-checked-word-seal-publication-checkpoint-20261011-02';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-checked-word-seal-checkpoint-20261011-03/preservation_check.py').read_bytes())
print({'fresh_reports':3,'inherited_reports':1133,'owned_modules':136,'counts_derived_from_originals':True})
