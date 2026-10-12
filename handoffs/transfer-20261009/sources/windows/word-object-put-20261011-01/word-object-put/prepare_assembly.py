from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-layer-flatten-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-layer-flatten-20261011-03'","CURRENT = DIAG / 'transfer-word-object-put-20261011-03'"),
 ("MODULE = 'TransferWordLayerFlatten01'","MODULE = 'TransferWordObjectPut01'"),
 ("CHECKPOINT = DIAG / 'transfer-word-layer-flatten-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-word-object-put-checkpoint-20261011-03'"),
 ('assert len(fresh) == 4','assert len(fresh) == 8'),
 ("assert pool['objects'] == 124 and len(pool['inherited_public_reports']) == 1059","assert pool['objects'] == 125 and len(pool['inherited_public_reports']) == 1063"),
 ("manager_endpoint = DIAG / 'transfer-word-layered-object-read-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-word-layer-flatten-endpoint-20261011-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-layered-object-read-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-layer-flatten-endpoint01.tar.xz'"),
 ('0f12778b2350f37e70a681f75a1291ef9445d76e6aae351e6d2956a9e1eb6bc6','bce2913d5b200269c695776982274d49974db229d719ea6a410c35124a2215f6'),
 ("tar.extractfile('reports/fresh-8-complete-declarations.txt')","tar.extractfile('reports/fresh-4-complete-declarations.txt')"),
 ('assert len(manager_reports) == 8','assert len(manager_reports) == 4'),
 ("'module': 'TransferWordLayeredObjectRead01'","'module': 'TransferWordLayerFlatten01'"),
 ('assert len(combined_reports) == 1059','assert len(combined_reports) == 1063'),
 ('assert len(manager_selected) == 124','assert len(manager_selected) == 125'),
 ("reference = {'word_layered_object_read':","reference = {'word_layer_flatten':"),
 ("'imported_complete_reports': 8","'imported_complete_reports': 4"),
 ("'complete_owned_modules': 124, 'inherited_complete_reports': 1059","'complete_owned_modules': 125, 'inherited_complete_reports': 1063"),
 ("'fresh_definition_audits': 0","'fresh_definition_audits': 3"),
 ("'fresh_theorem_audits': 4","'fresh_theorem_audits': 5"),
 ("'fresh_complete_public_audits': 4","'fresh_complete_public_audits': 8"),
 ("'inherited_complete_public_audits': 1059","'inherited_complete_public_audits': 1063"),
 ("archive = ROOT / 'portable-windows-word-layer-flatten-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-object-put-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-4-complete-declarations.txt'","add(stdout, 'reports/fresh-8-complete-declarations.txt'")]:replace(a,b)
replace("'fresh_audits': 4, 'inherited_audits': 1059","'fresh_audits': 8, 'inherited_audits': 1063",2)
s=s.replace('transfer-word-layer-flatten-endpoint-v1','transfer-word-object-put-endpoint-v1').replace('one-hundred-twenty-four-module','one-hundred-twenty-five-module').replace('1059 original inherited','1063 original inherited').replace('verified 1059 inherited','verified 1063 inherited')
s=s.replace('CHECKED_WORD_LOOKUP_EQUALS_FUNCTIONAL_LAYER_APPLICATION_AND_FLATTEN_QUALIFIED','FIXED_PENDING_TYPE_GUARDED_OBJECT_PUT_AND_CHECKED_READ_QUALIFIED')
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['saturating_capacity_source_shape']",start)
history="""for attempt in [1,2]:
    failed=DIAG/('transfer-word-object-put-20261011-'+str(attempt).zfill(2))
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordObjectPut01.lean','project/ShielddSecurity/TransferWordObjectPut01.lean','context/checked-pending-put-shape.json']
    if attempt==1:names.append('runs/01-TransferWordObjectPut01/stdout.txt')
    for name in names:
        assert pin(failed/name) in plan['pins']
        add(failed/name,'unselected/'+str(attempt).zfill(2)+'/'+name,'original unsolved conditional equality01 or pre-Lean pressure02 retained; entire failed attempt zero proof/native/control credit including incomplete sorryAx output')
row=mapping['checked_pending_put_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'],'context/checked-pending-put-shape.json','exact source inner Any TypeId read and mismatch panic before boxed pending object insert; static association only')
"""
s=s[:start]+history+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained, three definitions/five theorems. Type-match Bool observes expected pending enum type, with same type for Open/Sealed. Absent/tombstoned or correct existing enum permits boxed put; previous wrong type panics before mutation. Successful modeled update derives exact latest write and other-key frame, then supported sealed codec derives checked read. Failed01 unsolved conditional equality and failed02 pre-Lean pressure retained as twenty-one complete raw files, all incomplete sorryAx reports zero credit. Fresh03 same repaired source as02 with direct conditional proof, unchanged limits/guards. Actual TypeId/inner Box/Any/Clone/map/locks/compiler/ownership and whole-program primitive correspondence remain explicit. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':1063,'owned_modules':125,'history_files':21})
