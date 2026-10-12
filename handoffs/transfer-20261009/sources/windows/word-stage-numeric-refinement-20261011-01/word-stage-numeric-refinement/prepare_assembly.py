from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-stage-admission-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-stage-admission-20261011-02'","CURRENT = DIAG / 'transfer-word-stage-numeric-refinement-20261011-03'"),
 ("MODULE = 'TransferWordStageAdmission01'","MODULE = 'TransferWordStageNumericRefinement01'"),
 ("CHECKPOINT = DIAG / 'transfer-word-stage-admission-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-word-stage-numeric-refinement-checkpoint-20261011-03'"),
 ("manager_endpoint = DIAG / 'transfer-word-stage-order-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-word-stage-admission-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-stage-order-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-stage-admission-endpoint01.tar.xz'"),
 ('c0b4b515bec54e0b50dfeda26dfaaa94951d0a0b3e31626c8fdd6db4039856f7','a07959d62c4e14f14384019549bb389c312c2da0365ecff2f7477a9c0159606b'),
 ("tar.extractfile('reports/fresh-8-complete-declarations.txt')","tar.extractfile('reports/fresh-6-complete-declarations.txt')"),
 ('assert len(manager_reports) == 8','assert len(manager_reports) == 6'),
 ("'module': 'TransferWordStageOrder01'","'module': 'TransferWordStageAdmission01'"),
 ("reference = {'word_stage_order':","reference = {'word_stage_admission':"),
 ("'imported_complete_reports': 8","'imported_complete_reports': 6")]:replace(a,b)
s=s.replace('131','132').replace('1101','1107')
replace("assert declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 6","assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 4")
s=s.replace('transfer-word-stage-admission-endpoint-v1','transfer-word-stage-numeric-refinement-endpoint-v1').replace('one-hundred-thirty-one-module','one-hundred-thirty-two-module').replace('RETURNED_CANONICAL_WORD_STAGE_DERIVES_ALL_ADMISSION_AND_ORIGINAL_FIELDS_QUALIFIED','TYPED_OPEN_WORD_STAGE_EXACT_NUMERIC_INSPECTION_AND_DURABLE_OBSERVATIONS_QUALIFIED')
replace("archive = ROOT / 'portable-windows-word-stage-admission-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-stage-numeric-refinement-endpoint01.tar.xz'")
replace("'rejected_attempts': 1","'rejected_attempts': 2")
start=s.index("pressure=DIAG/'transfer-word-stage-admission-20261011-01'");end=s.index("row=mapping['sct_pending_read_source_shape']",start)
s=s[:start]+"for attempt in [1,2]:\n    failed=DIAG/('transfer-word-stage-numeric-refinement-20261011-0'+str(attempt))\n    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordStageNumericRefinement01.lean','project/ShielddSecurity/TransferWordStageNumericRefinement01.lean']\n    if attempt==2:names.append('runs/01-TransferWordStageNumericRefinement01/stdout.txt')\n    for name in names:\n        row=pin(failed/name)\n        assert row in plan['pins']\n        add(failed/name,'rejected-numeric-attempt0'+str(attempt)+'/'+name,'exact original pressure or Lean error/warning/sorryAx output; entire failed attempt zero credit')\n"+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete audits retained, two definitions/four theorems. Typed Open source-word staging with concrete modeled reader has exact numeric inspection refusal/success followed by original field write. Returned stage derives exact numeric pending append and all modeled durable statuses false plus prior pending absence. Explicit previous typed-Open constructor remains domain; not arbitrary Any. Initial pressure and second Lean error/warning/sorryAx attempts preserve 19 original raw artifacts with entire attempts zero credit. Proof-search-only spelling/branch/witness repair, definitions/contracts/guards unchanged. Native bindings OPEN; no native/control/certification or accepted ancestor replay credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-word-stage-numeric-refinement-checkpoint-20261011-03';checkpoint.mkdir(exist_ok=False)
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-word-stage-admission-checkpoint-20261011-02/preservation_check.py').read_bytes())
print({'fresh_reports':6,'inherited_reports':1107,'owned_modules':132,'failed_attempts':2})
