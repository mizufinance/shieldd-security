from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-stage-numeric-refinement-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-stage-numeric-refinement-20261011-03'","CURRENT = DIAG / 'transfer-checked-word-stage-refinement-20261011-04'"),
 ("MODULE = 'TransferWordStageNumericRefinement01'","MODULE = 'TransferCheckedWordStageRefinement01'"),
 ("CHECKPOINT = DIAG / 'transfer-word-stage-numeric-refinement-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-checked-word-stage-refinement-checkpoint-20261011-04'"),
 ("manager_endpoint = DIAG / 'transfer-word-stage-admission-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-word-stage-numeric-refinement-endpoint-20261011-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-stage-admission-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-stage-numeric-refinement-endpoint01.tar.xz'"),
 ('a07959d62c4e14f14384019549bb389c312c2da0365ecff2f7477a9c0159606b','9bd6301940c7652faa22d8defa56a16784f6264906e748b23f91a2ef6ab1a39a'),
 ("'module': 'TransferWordStageAdmission01'","'module': 'TransferWordStageNumericRefinement01'"),
 ("reference = {'word_stage_admission':","reference = {'word_stage_numeric_refinement':")]:replace(a,b)
s=s.replace('132','133').replace('1107','1113')
replace('assert len(fresh) == 6','assert len(fresh) == 8')
replace("assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 4","assert declaration_kinds.count('def') == 4 and declaration_kinds.count('theorem') == 4")
replace("add(stdout, 'reports/fresh-6-complete-declarations.txt'","add(stdout, 'reports/fresh-8-complete-declarations.txt'")
replace("'fresh_complete_public_audits': 6","'fresh_complete_public_audits': 8")
replace("'fresh_audits': 6, 'inherited_audits': 1113","'fresh_audits': 8, 'inherited_audits': 1113",2)
s=s.replace('transfer-word-stage-numeric-refinement-endpoint-v1','transfer-checked-word-stage-refinement-endpoint-v1').replace('one-hundred-thirty-two-module','one-hundred-thirty-three-module').replace('TYPED_OPEN_WORD_STAGE_EXACT_NUMERIC_INSPECTION_AND_DURABLE_OBSERVATIONS_QUALIFIED','ALL_CHECKED_WORD_STAGE_BRANCHES_REFINE_CHECKED_NUMERIC_OUTCOMES_QUALIFIED')
replace("archive = ROOT / 'portable-windows-word-stage-numeric-refinement-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-stage-refinement-endpoint01.tar.xz'")
replace("'rejected_attempts': 2","'rejected_attempts': 3")
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['sct_pending_read_source_shape']",start)
s=s[:start]+"for attempt in [1,2]:\n    failed=DIAG/('transfer-checked-word-stage-refinement-20261011-0'+str(attempt))\n    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordStageRefinement01.lean','project/ShielddSecurity/TransferCheckedWordStageRefinement01.lean','runs/01-TransferCheckedWordStageRefinement01/stdout.txt']\n    for name in names:\n        row=pin(failed/name)\n        assert row in plan['pins']\n        add(failed/name,'rejected-checked-stage-attempt0'+str(attempt)+'/'+name,'exact original Lean type/let errors, warning/sorryAx output; entire failed attempt zero credit')\nunrun=DIAG/'transfer-checked-word-stage-refinement-20261011-03'\nassert not (unrun/'plan.json').exists() and not (unrun/'events.jsonl').exists()\nfor name in ['prepare_recipe.py','prepare.py']:\n    row=pin(unrun/name)\n    assert row in plan['pins']\n    add(unrun/name,'unrun-checked-stage-setup03/'+name,'original setup indentation transformation assertion before plan/Lean; zero credit')\nadd(CURRENT/'repair_recipe.py','qualified/repair_recipe.py','exact fresh setup repair source, generation only; prepared source and plan are compile inputs')\n"+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete audits retained, four definitions/four theorems. All source previous-object branches stage to checked numeric inspection with actual previous-membership reader and outer wrong-type panic retained; caller supplies no typed-Open/getter/inverse/admission/desired-next-object premise. Original word append projects to exact numeric append. Pure uniqueness is repeated inside numeric wrapper: semantic outcome equality, no native identical-trace claim. First phantom-type and second let/projection errors preserve20 original raw artifacts plus setup03 two unrun source recipes; all failed/unrun attempts zero credit, proof-search/type/indentation repairs only. Native bindings OPEN; no native/control/certification or accepted ancestor replay credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-checked-word-stage-refinement-checkpoint-20261011-04';checkpoint.mkdir(exist_ok=False)
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-word-stage-numeric-refinement-checkpoint-20261011-03/preservation_check.py').read_bytes())
print({'fresh_reports':8,'inherited_reports':1113,'owned_modules':133,'rejected_proof_attempts':2,'unrun_setup':1})
